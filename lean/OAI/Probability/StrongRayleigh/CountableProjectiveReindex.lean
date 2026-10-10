import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139.CountableProjectiveReindex

variable {I : Type u_1} {J : Type u_2} {E : Type u_3} [MeasurableSpace E]

def imageEquiv (e : J ≃ I) (S : Finset J) : S ≃ S.map e.toEmbedding :=
  Equiv.subtypeEquiv e (by intro i; simp)

@[simp] lemma imageEquiv_apply_val (e : J ≃ I) (S : Finset J) (i : S) :
    ((imageEquiv e S i : S.map e.toEmbedding) : I) = e i := rfl

@[simp] lemma imageEquiv_symm_apply_val (e : J ≃ I) (S : Finset J)
    (i : S.map e.toEmbedding) :
    ((imageEquiv e S).symm i : J) = e.symm i := by
  apply e.injective
  rw [e.apply_symm_apply]
  exact congrArg Subtype.val ((imageEquiv e S).apply_symm_apply i)

def coordinatePullback (e : J ≃ I) : (I → E) ≃ᵐ (J → E) where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp
  measurable_toFun := Measurable.of_eval fun _ => measurable_pi_apply _
  measurable_invFun := Measurable.of_eval fun _ => measurable_pi_apply _

def finitePullback (e : J ≃ I) (S : Finset J) :
    (S.map e.toEmbedding → E) ≃ᵐ (S → E) :=
  coordinatePullback (imageEquiv e S)

def reindexFamily (e : J ≃ I)
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (S : Finset J) : ProbabilityMeasure (S → E) :=
  (P (S.map e.toEmbedding)).map (finitePullback (E := E) e S)

lemma reindexFamily_projective (e : J ≃ I)
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E) (fun S => (P S : Measure (S → E)))) :
    IsProjectiveMeasureFamily (α := fun _ => E) (fun S => (reindexFamily e P S : Measure (S → E))) := by
  intro S T hTS
  change ((P (T.map e.toEmbedding) : Measure _).map (finitePullback (E := E) e T)) =
    (((P (S.map e.toEmbedding) : Measure _).map (finitePullback (E := E) e S)).map
      (Finset.restrict₂ (π := fun _ => E) hTS))
  have hp := hP (S.map e.toEmbedding) (T.map e.toEmbedding)
    (Finset.map_subset_map.mpr hTS)
  dsimp only at hp
  rw [hp]
  have hr : Measurable (Finset.restrict₂ (π := fun _ => E) hTS) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  have hr' : Measurable (Finset.restrict₂ (π := fun _ => E)
      (Finset.map_subset_map.mpr hTS : T.map e.toEmbedding ⊆ S.map e.toEmbedding)) :=
    Measurable.of_eval fun _ => measurable_pi_apply _
  rw [Measure.map_map (finitePullback (E := E) e T).measurable hr',
    Measure.map_map hr (finitePullback (E := E) e S).measurable]
  congr 1

lemma projectiveLimit_reindex (e : J ≃ I)
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (μ : ProbabilityMeasure (J → E))
    (hμ : IsProjectiveLimit (α := fun _ => E) (μ : Measure (J → E))
      (fun S => (reindexFamily e P S : Measure (S → E)))) :
    IsProjectiveLimit (α := fun _ => E)
      ((μ.map (coordinatePullback (E := E) e).symm :
        ProbabilityMeasure (I → E)) : Measure (I → E))
      (fun S => (P S : Measure (S → E))) := by
  intro S
  obtain ⟨T, rfl⟩ := e.finsetCongr.surjective S
  change (((μ : Measure (J → E)).map (coordinatePullback (E := E) e).symm).map
    (T.map e.toEmbedding).restrict) = (P (T.map e.toEmbedding) : Measure _)
  have hcomp : (T.map e.toEmbedding).restrict ∘ (coordinatePullback (E := E) e).symm =
      (finitePullback (E := E) e T).symm ∘ T.restrict := by
    funext x i
    change x (e.symm i) = x ((imageEquiv e T).symm i)
    rw [imageEquiv_symm_apply_val]
  rw [Measure.map_map (by fun_prop) (coordinatePullback (E := E) e).symm.measurable,
    hcomp, ← Measure.map_map (finitePullback (E := E) e T).symm.measurable (by fun_prop), hμ T]
  change (((P (T.map e.toEmbedding) : Measure _).map (finitePullback (E := E) e T)).map
    (finitePullback (E := E) e T).symm) = _
  rw [Measure.map_map (finitePullback (E := E) e T).symm.measurable (finitePullback (E := E) e T).measurable]
  simp only [Function.comp_def, MeasurableEquiv.symm_apply_apply]
  exact Measure.map_id

lemma finite_projective_exists [Finite I]
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E) (fun S => (P S : Measure (S → E)))) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (I → E)) (fun S => (P S : Measure (S → E))) := by
  classical
  let := Fintype.ofFinite I
  let f : (↥(Finset.univ : Finset I) → E) → (I → E) := fun x i => x ⟨i, Finset.mem_univ i⟩
  have hf : Measurable f := Measurable.of_eval fun _ => measurable_pi_apply _
  refine ⟨(P Finset.univ).map f, ?_⟩
  intro S
  change (((P Finset.univ : Measure (↥(Finset.univ : Finset I) → E)).map f).map
    S.restrict) = (P S : Measure (S → E))
  rw [Measure.map_map (by fun_prop) hf]
  exact (hP Finset.univ S (Finset.subset_univ S)).symm

lemma countable_projective_exists_of_nat [Countable I]
    (natExtension : ∀ P : (S : Finset ℕ) → ProbabilityMeasure (S → E),
      IsProjectiveMeasureFamily (α := fun _ => E) (fun S => (P S : Measure (S → E))) →
      ∃ μ : ProbabilityMeasure (ℕ → E),
        IsProjectiveLimit (α := fun _ => E) (μ : Measure (ℕ → E)) (fun S => (P S : Measure (S → E))))
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E) (fun S => (P S : Measure (S → E)))) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (I → E)) (fun S => (P S : Measure (S → E))) := by
  cases finite_or_infinite I with
  | inl h => exact finite_projective_exists P hP
  | inr h =>
      let e : ℕ ≃ I := Classical.choice inferInstance
      obtain ⟨μ, hμ⟩ := natExtension (reindexFamily e P) (reindexFamily_projective e P hP)
      exact ⟨μ.map (coordinatePullback (E := E) e).symm,
        projectiveLimit_reindex e P μ hμ⟩

end Problem336AdditiveD139.CountableProjectiveReindex

end

end OAI
