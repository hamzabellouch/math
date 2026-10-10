import OAI.Probability.StrongRayleigh.BinaryProjective

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open MeasureTheory

namespace Problem336AdditiveD139.CantorProjective

variable {I : Type u_1} {E : Type u_2} [MeasurableSpace E]

def sites (A : Finset (I × ℕ)) : Finset I := by
  classical
  exact A.image Prod.fst

lemma mem_sites {A : Finset (I × ℕ)} (a : A) : a.1.1 ∈ sites A := by
  classical
  exact Finset.mem_image.mpr ⟨a.1, a.2, rfl⟩

lemma sites_mono {A B : Finset (I × ℕ)} (h : B ⊆ A) : sites B ⊆ sites A := by
  classical
  exact Finset.image_subset_image h

def extract (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ))
    (x : sites A → E) : A → Bool :=
  fun a => e (x ⟨a.1.1, mem_sites a⟩) a.1.2

lemma measurable_extract (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ)) :
    Measurable (extract e A) := by
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.1.2).comp
    (e.measurable.comp (measurable_pi_apply (⟨a.1.1, mem_sites a⟩ : sites A)))

def bitFamily (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) (A : Finset (I × ℕ)) : Measure (A → Bool) :=
  (P (sites A)).map (extract e A)

instance bitFamily_isProbabilityMeasure (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (A : Finset (I × ℕ)) : IsProbabilityMeasure (bitFamily e P A) :=
  by unfold bitFamily; infer_instance

lemma bitFamily_projective (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    IsProjectiveMeasureFamily (α := fun _ : I × ℕ => Bool) (bitFamily e P) := by
  intro A B hBA
  unfold bitFamily
  rw [hP (sites A) (sites B) (sites_mono hBA)]
  rw [Measure.map_map (measurable_extract e B) (Finset.measurable_restrict₂ _),
    Measure.map_map (Finset.measurable_restrict₂ (X := fun _ : I × ℕ => Bool) hBA)
      (measurable_extract e A)]
  congr 1

theorem exists_bit_limit (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    ∃ μ : ProbabilityMeasure ((I × ℕ) → Bool),
      IsProjectiveLimit (α := fun _ : I × ℕ => Bool) (μ : Measure ((I × ℕ) → Bool)) (bitFamily e P) :=
  binary_projective_exists (bitFamily e P) (bitFamily_projective e P hP)

def extractFrom (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ)) (S : Finset I)
    (hAS : sites A ⊆ S) (x : S → E) : A → Bool :=
  fun a => e (x ⟨a.1.1, hAS (mem_sites a)⟩) a.1.2

lemma measurable_extractFrom (e : E ≃ᵐ (ℕ → Bool)) (A : Finset (I × ℕ))
    (S : Finset I) (hAS : sites A ⊆ S) : Measurable (extractFrom e A S hAS) := by
  apply Measurable.of_eval
  intro a
  exact (measurable_pi_apply a.1.2).comp
    (e.measurable.comp (measurable_pi_apply (⟨a.1.1, hAS (mem_sites a)⟩ : S)))

lemma bitFamily_eq_map_of_sites_subset (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (A : Finset (I × ℕ)) (S : Finset I) (hAS : sites A ⊆ S) :
    bitFamily e P A = (P S).map (extractFrom e A S hAS) := by
  unfold bitFamily
  rw [hP S (sites A) hAS,
    Measure.map_map (measurable_extract e A) (Finset.measurable_restrict₂ _)]
  rfl

theorem map_finite_observations (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P))
    {F : Type u_3} [Fintype F] (f : F → I × ℕ) (S : Finset I)
    (hf : ∀ a, (f a).1 ∈ S) :
    μ.map (fun b a => b (f a)) =
      (P S).map (fun x a => e (x ⟨(f a).1, hf a⟩) (f a).2) := by
  classical
  let A : Finset (I × ℕ) := Finset.univ.image f
  have hA (a : F) : f a ∈ A := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hAS : sites A ⊆ S := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    exact hf a
  let r : (A → Bool) → F → Bool := fun b a => b ⟨f a, hA a⟩
  have hr : Measurable r := Measurable.of_eval (fun a => measurable_pi_apply _)
  calc
    μ.map (fun b a => b (f a)) = (μ.map A.restrict).map r := by
      rw [Measure.map_map hr (Finset.measurable_restrict _)]
      rfl
    _ = (bitFamily e P A).map r := by rw [hμ A]
    _ = ((P S).map (extractFrom e A S hAS)).map r := by
      rw [bitFamily_eq_map_of_sites_subset e P hP A S hAS]
    _ = (P S).map (fun x a => e (x ⟨(f a).1, hf a⟩) (f a).2) := by
      rw [Measure.map_map hr (measurable_extractFrom e A S hAS)]
      rfl

def encodeEquiv (e : E ≃ᵐ (ℕ → Bool)) (J : Type u_4) :
    (J → E) ≃ᵐ ((J × ℕ) → Bool) where
  toFun x p := e (x p.1) p.2
  invFun b j := e.symm (fun n => b (j, n))
  left_inv x := by ext j; exact e.symm_apply_apply (x j)
  right_inv b := by ext p; exact congrFun (e.apply_symm_apply (fun n => b (p.1, n))) p.2
  measurable_toFun := by
    exact Measurable.of_eval (fun p => (measurable_pi_apply p.2).comp
      (e.measurable.comp (measurable_pi_apply p.1)))
  measurable_invFun := by
    exact Measurable.of_eval (fun j => e.symm.measurable.comp
      (Measurable.of_eval (fun n => measurable_pi_apply (j, n))))

theorem encoded_marginal (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P))
    (S : Finset I) :
    μ.map (fun b (p : S × ℕ) => b (p.1.1, p.2)) =
      (P S).map (encodeEquiv e S) := by
  let Q : Measure ((S × ℕ) → Bool) := (P S).map (encodeEquiv e S)
  have hQ : IsProjectiveLimit (α := fun _ : S × ℕ => Bool) Q
      (fun A => Q.map A.restrict) := fun _ => rfl
  apply IsProjectiveLimit.unique (P := fun A => Q.map A.restrict) ?_ hQ
  intro A
  dsimp only [Q]
  have hm : Measurable (fun (b : (I × ℕ) → Bool) (p : S × ℕ) =>
      b (p.1.1, p.2)) := by fun_prop
  rw [Measure.map_map (Finset.measurable_restrict A) hm,
    Measure.map_map (Finset.measurable_restrict A) (encodeEquiv e S).measurable]
  exact map_finite_observations e P hP μ hμ
    (fun a : A => (a.1.1.1, a.1.2)) S (fun a => a.1.1.2)

theorem decoded_isProjectiveLimit (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P)
    (μ : Measure ((I × ℕ) → Bool))
    (hμ : IsProjectiveLimit (α := fun _ : I × ℕ => Bool) μ (bitFamily e P)) :
    IsProjectiveLimit (α := fun _ : I => E)
      (μ.map (encodeEquiv e I).symm) P := by
  intro S
  apply (encodeEquiv e S).measurableEmbedding.map_injective
  rw [Measure.map_map (Finset.measurable_restrict S) (encodeEquiv e I).symm.measurable,
    Measure.map_map (encodeEquiv e S).measurable
      ((Finset.measurable_restrict S).comp (encodeEquiv e I).symm.measurable)]
  have heq : (encodeEquiv e S) ∘ (S.restrict ∘ (encodeEquiv e I).symm) =
      (fun b (p : S × ℕ) => b (p.1.1, p.2)) := by
    funext b p
    exact congrFun (e.apply_symm_apply (fun n => b (p.1.1, n))) p.2
  rw [heq]
  exact encoded_marginal e P hP μ hμ S

theorem projective_exists_of_cantor_equiv (e : E ≃ᵐ (ℕ → Bool))
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => E) P) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ : I => E) (μ : Measure (I → E)) P := by
  obtain ⟨μ, hμ⟩ := exists_bit_limit e P hP
  refine ⟨μ.map (encodeEquiv e I).symm, ?_⟩
  exact decoded_isProjectiveLimit e P hP (μ : Measure _) hμ

theorem real_projective_exists
    (P : (S : Finset I) → Measure (S → ℝ)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ : I => ℝ) P) :
    ∃ μ : ProbabilityMeasure (I → ℝ),
      IsProjectiveLimit (α := fun _ : I => ℝ) (μ : Measure (I → ℝ)) P :=
  projective_exists_of_cantor_equiv
    (PolishSpace.measurableEquivNatBoolOfNotCountable (α := ℝ) not_countable) P hP

end Problem336AdditiveD139.CantorProjective

end

end OAI
