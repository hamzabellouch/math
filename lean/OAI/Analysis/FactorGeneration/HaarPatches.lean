import OAI.Analysis.FactorGeneration.LocalPatches

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! The same ordered signed words in any star algebra, with exact transport
through bounded sequence evaluation and the actual quotient homomorphism. -/
section
open UltrapowerBridge

def algebraSignedLetter {A : Type*} [Star A] (v : A) (s : Bool) : A :=
  if s then star v else v

def algebraPatchingWord {A : Type*} [Monoid A] [Star A] (v : A) :
    List (Bool × A) → A
  | [] => 1
  | (s,x)::xs => algebraSignedLetter v s*x*algebraPatchingWord v xs

def optionalCoefficient {A : Type*} [One A] (x : ℕ → A) : Option ℕ → A
  | none => 1
  | some i => x i

theorem map_algebraPatchingWord {A B : Type*} [Ring A] [Ring B]
    [StarRing A] [StarRing B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →⋆ₐ[ℂ] B) (v : A) (xs : List (Bool × A)) :
    f (algebraPatchingWord v xs) =
      algebraPatchingWord (f v) (xs.map (fun a => (a.1,f a.2))) := by
  induction xs with
  | nil => exact f.map_one
  | cons a xs ih =>
    simp only [algebraPatchingWord,List.map_cons,map_mul,ih]
    congr 2
    cases a.1
    · rfl
    · exact map_star f v

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem algebraPatchingWord_eq (v : M.toStarSubalgebra)
    (xs : List (Bool × M.toStarSubalgebra)) :
    algebraPatchingWord v xs = patchingWord v xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [algebraPatchingWord,patchingWord,ih,algebraSignedLetter,signedLetter]

def boundedEvaluation (j : ℕ) : Bounded M →⋆ₐ[ℂ] M.toStarSubalgebra where
  toFun a := a.val j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

theorem bounded_word_evaluation (v : Bounded M) (xs : List (Bool × Bounded M)) (j : ℕ) :
    (algebraPatchingWord v xs).val j =
      patchingWord (v.val j) (xs.map (fun a => (a.1,a.2.val j))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (algebraSignedLetter v a.1).val j * a.2.val j *
      (algebraPatchingWord v xs).val j = _
    rw [ih]
    simp only [List.map_cons,patchingWord]
    cases a.1 <;> rfl

end

/-! The finite-error f=1 conclusion of Popa Lemma 3.2, for the irreducible
scalar-commutant inclusion with the explicit represented-factor hypotheses. -/
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem patchingTolerance_scale (δ : ℝ) (k : ℕ) :
    patchingTolerance δ k=δ*patchingTolerance 1 k := by
  induction k with
  | zero => simp
  | succ k ih => rw [patchingTolerance_succ,patchingTolerance_succ,ih]; ring

def diagonalCoefficientFamily (x : ℕ → ℕ → M.toStarSubalgebra) (j : ℕ) : Finset M.toStarSubalgebra := by
  classical
  exact (Finset.range (j+1)).image (fun i => x i j)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

theorem exists_finite_partial_independence
    (F : Finset M.toStarSubalgebra) (hF : ∀ x ∈ F,‖x‖ ≤ 1)
    (hcenter : ∀ x ∈ F,τ.trace x=0) (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : PartialUnitary M,v.val.val ∈ N ∧ 1/4 < (τ.trace v.support.val).re ∧
      ∀ x₀ ∈ (F : Set M.toStarSubalgebra) ∪ {1},∀ xs : List (Bool × M.toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ n → patchingCoefficients (F : Set M.toStarSubalgebra) xs →
        ‖τ.trace (x₀*patchingWord v.val xs)‖ ≤ ε := by
  let δ := ε/patchingTolerance 1 n
  have ht := patchingTolerance_pos 1 (by norm_num) n
  have hδ : 0 < δ := div_pos hε ht
  obtain ⟨v,hv,hs⟩ := exists_large_admissible_partialUnitary τ hNM hfactor hdiff hirr hsep
    F hF hcenter n δ hδ
  have he : patchingTolerance δ n=ε := by
    rw [patchingTolerance_scale]
    exact div_mul_cancel₀ ε ht.ne'
  refine ⟨v,hv.2,hs,?_⟩
  intro x₀ hx₀ xs hpos hn hc
  have hh := hv.1.2 x₀ hx₀ xs hpos hn hc
  have hmono := patchingTolerance_mono δ hδ hn
  rw [he] at hmono
  exact hh.trans ((mul_le_of_le_one_right (patchingTolerance_pos δ hδ xs.length).le
    (PartialUnitary.support_trace_le_one τ v)).trans hmono)

/-- A genuine diagonal sequence for a countable family of varying centered
contractions; the coefficient at stage j may depend on j. This is still a
partial-unitary construction, not a full free Haar unitary. -/
theorem exists_diagonal_partial_independence
    (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
    (hc : ∀ i j,τ.trace (x i j)=0) :
    ∃ v : ℕ → PartialUnitary M,∀ j,
      (v j).val.val ∈ N ∧ 1/4 < (τ.trace (v j).support.val).re ∧
      ∀ a ∈ (diagonalCoefficientFamily x j : Set M.toStarSubalgebra) ∪ {1},
      ∀ xs : List (Bool × M.toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ j+1 →
        patchingCoefficients (diagonalCoefficientFamily x j : Set M.toStarSubalgebra) xs →
        ‖τ.trace (a*patchingWord (v j).val xs)‖ ≤ 1/((j : ℝ)+1) := by
  classical
  have hstage : ∀ j,∃ v : PartialUnitary M,v.val.val ∈ N ∧ 1/4 < (τ.trace v.support.val).re ∧
      ∀ a ∈ (diagonalCoefficientFamily x j : Set M.toStarSubalgebra) ∪ {1},
      ∀ xs : List (Bool × M.toStarSubalgebra),
        1 ≤ xs.length → xs.length ≤ j+1 →
        patchingCoefficients (diagonalCoefficientFamily x j : Set M.toStarSubalgebra) xs →
        ‖τ.trace (a*patchingWord v.val xs)‖ ≤ 1/((j : ℝ)+1) := by
    intro j
    apply exists_finite_partial_independence τ hNM hfactor hdiff hirr hsep
      (diagonalCoefficientFamily x j) ?_ ?_ (j+1) _ (by positivity)
    · intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hx i j
    · intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      exact hc i j
  choose v hv using hstage
  exact ⟨v,hv⟩

end

/-! A countable diagonal construction with actual vanishing ordered moments.
The countable coefficients may vary with the sequence coordinate. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def indexedCoefficient (x : ℕ → ℕ → M.toStarSubalgebra) (j : ℕ) :
    Option ℕ → M.toStarSubalgebra
  | none => 1
  | some i => x i j

theorem eventually_list_indices (is : List ℕ) : ∀ᶠ j : ℕ in atTop,∀ i ∈ is,i ≤ j := by
  induction is with
  | nil => exact Eventually.of_forall (fun _ => by simp)
  | cons i is ih =>
    filter_upwards [ih,eventually_ge_atTop i] with j hj hi
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hi
    · exact hj a ha

theorem eventually_indexedCoefficient (x : ℕ → ℕ → M.toStarSubalgebra) (i : Option ℕ) :
    ∀ᶠ j : ℕ in atTop,indexedCoefficient x j i ∈
      (diagonalCoefficientFamily x j : Set M.toStarSubalgebra) ∪ {1} := by
  classical
  cases i with
  | none => exact Eventually.of_forall (fun _ => Or.inr rfl)
  | some i =>
    filter_upwards [eventually_ge_atTop i] with j hj
    exact Or.inl (Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr (by omega),rfl⟩)

variable (hNM : N ≤ M)
variable (hfactor : ∀ c : N.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
variable (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hirr : ∀ c : M.toStarSubalgebra,
  (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
  ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
variable (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
include hfactor hdiff hirr hsep

/-- Every nonempty source word is encoded by its internal index list, final
sign and two optional endpoint indices. None represents exactly the unit. -/
theorem exists_countable_partial_independence
    (x : ℕ → ℕ → M.toStarSubalgebra) (hx : ∀ i j,‖x i j‖ ≤ 1)
    (hc : ∀ i j,τ.trace (x i j)=0) :
    ∃ v : ℕ → PartialUnitary M,
      (∀ j,(v j).val.val ∈ N) ∧ (∀ j,1/4 < (τ.trace (v j).support.val).re) ∧
      ∀ first last : Option ℕ,∀ xs : List (Bool × ℕ),∀ s : Bool,
        Tendsto (fun j => τ.trace (indexedCoefficient x j first * patchingWord (v j).val
          (xs.map (fun a => (a.1,x a.2 j)) ++ [(s,indexedCoefficient x j last)]))) atTop (𝓝 0) := by
  classical
  obtain ⟨v,hv⟩ := exists_diagonal_partial_independence τ hNM hfactor hdiff hirr hsep x hx hc
  refine ⟨v,fun j => (hv j).1,fun j => (hv j).2.1,?_⟩
  intro first last xs s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [eventually_list_indices (xs.map Prod.snd),eventually_ge_atTop xs.length,
    eventually_indexedCoefficient x first,eventually_indexedCoefficient x last] with j hj hlen hfirst hlast
  apply (hv j).2.2 _ hfirst _ (by simp) (by simpa using Nat.add_le_add_right hlen 1)
  apply patchingCoefficients_append_endpoint _ _ ?_ (s,indexedCoefficient x j last) hlast
  intro a ha
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
  exact Finset.mem_image.mpr ⟨b.2,Finset.mem_range.mpr (by
    have hh := hj b.2 (List.mem_map.mpr ⟨b,hb,rfl⟩)
    omega),rfl⟩

end

/-! Actual positive-support partial independence in the bounded-sequence
tracial quotient. Freeness is expressed by domination of atTop. -/
open Filter
open scoped Topology
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

def boundedPartialUnitary (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).val,1,zero_le_one,fun j => (v j).unitary.norm_le_one⟩

def boundedPartialSupport (v : ℕ → PartialUnitary M) : Bounded M :=
  ⟨fun j => (v j).support.val,1,zero_le_one,fun j => (v j).support.property.norm_le⟩

theorem boundedPartialSupport_projection (v : ℕ → PartialUnitary M) :
    IsStarProjection (boundedPartialSupport v) := by
  constructor
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isIdempotentElem
  · apply Subtype.ext
    funext j
    exact (v j).support.property.isSelfAdjoint

theorem boundedPartialUnitary_initial (v : ℕ → PartialUnitary M) :
    star (boundedPartialUnitary v)*boundedPartialUnitary v = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.initial

theorem boundedPartialUnitary_final (v : ℕ → PartialUnitary M) :
    boundedPartialUnitary v*star (boundedPartialUnitary v) = boundedPartialSupport v := by
  apply Subtype.ext
  funext j
  exact (v j).unitary.final

theorem boundedPartialUnitary_inclusion (hNM : N ≤ M)
    (v : ℕ → PartialUnitary M) (hv : ∀ j,(v j).val.val ∈ N) :
    ∃ w : Bounded N,boundedInclusion hNM w = boundedPartialUnitary v := by
  refine ⟨⟨fun j => ⟨(v j).val.val,hv j⟩,1,zero_le_one,
    fun j => (v j).unitary.norm_le_one⟩,?_⟩
  rfl

theorem quotient_ordered_moment_zero (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (v : ℕ → PartialUnitary M) (x : ℕ → Bounded M)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool)
    (hz : Tendsto (fun j => τ.trace (indexedCoefficient (fun i => (x i).val) j first *
      patchingWord (v j).val (xs.map (fun a => (a.1,(x a.2).val j)) ++
        [(s,indexedCoefficient (fun i => (x i).val) j last)]))) atTop (𝓝 0)) :
    quotientTrace τ ω (optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) first *
      algebraPatchingWord (quotientMap τ (ω : Filter ℕ) (boundedPartialUnitary v))
        (xs.map (fun a => (a.1,quotientMap τ (ω : Filter ℕ) (x a.2))) ++
          [(s,optionalCoefficient (fun i => quotientMap τ (ω : Filter ℕ) (x i)) last)])) = 0 := by
  let f := quotientStarAlgHom τ (ω : Filter ℕ)
  let b : Bounded M := optionalCoefficient x first * algebraPatchingWord (boundedPartialUnitary v)
    (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)])
  have hopt (i : Option ℕ) : f (optionalCoefficient x i) =
      optionalCoefficient (fun i => f (x i)) i := by cases i <;> simp [optionalCoefficient]
  have hb : f b = optionalCoefficient (fun i => f (x i)) first *
      algebraPatchingWord (f (boundedPartialUnitary v))
        (xs.map (fun a => (a.1,f (x a.2))) ++ [(s,optionalCoefficient (fun i => f (x i)) last)]) := by
    simp only [b,map_mul,map_algebraPatchingWord,hopt,List.map_append,List.map_cons,List.map_nil,
      List.map_map,Function.comp_def]
  change quotientTrace τ ω (optionalCoefficient (fun i => f (x i)) first *
    algebraPatchingWord (f (boundedPartialUnitary v))
      (xs.map (fun a => (a.1,f (x a.2))) ++ [(s,optionalCoefficient (fun i => f (x i)) last)])) = 0
  rw [← hb]
  apply tendsto_nhds_unique (traceRep_tendsto τ ω b)
  have he (j : ℕ) : b.val j = indexedCoefficient (fun i => (x i).val) j first *
      patchingWord (v j).val (xs.map (fun a => (a.1,(x a.2).val j)) ++
        [(s,indexedCoefficient (fun i => (x i).val) j last)]) := by
    change (optionalCoefficient x first).val j * _ = _
    rw [bounded_word_evaluation]
    have ho (i : Option ℕ) : (optionalCoefficient x i).val j =
        indexedCoefficient (fun i => (x i).val) j i := by cases i <;> rfl
    simp only [ho,List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def]
    rfl
  simpa only [he] using hz.mono_left hω

end

/-! Exact multilinearity factors for ordered words; no factors are inverted
and signs affect only the partial-unitary letters. -/

theorem algebraPatchingWord_scale {A I : Type*} [Ring A] [Star A] [Algebra ℂ A]
    (v : A) (x y : I → A) (c : I → ℂ) (h : ∀ i,x i=c i • y i)
    (xs : List (Bool × I)) :
    algebraPatchingWord v (xs.map (fun a => (a.1,x a.2))) =
      (xs.map (fun a => c a.2)).prod •
        algebraPatchingWord v (xs.map (fun a => (a.1,y a.2))) := by
  induction xs with
  | nil => simp [algebraPatchingWord]
  | cons a xs ih =>
    simp only [List.map_cons,algebraPatchingWord,ih,List.prod_cons]
    rw [h a.2]
    simp only [
      mul_smul_comm,smul_mul_assoc,smul_smul,mul_comm (c a.2)]

theorem optionalCoefficient_scale {A : Type*} [Ring A] [Algebra ℂ A]
    (x y : ℕ → A) (c : ℕ → ℂ) (h : ∀ i,x i=c i • y i) (i : Option ℕ) :
    optionalCoefficient x i=optionalCoefficient c i • optionalCoefficient y i := by
  cases i <;> simp [optionalCoefficient,h]

theorem ordered_moment_scale {A : Type*} [Ring A] [Star A] [Algebra ℂ A]
    (v : A) (x y : ℕ → A) (c : ℕ → ℂ) (h : ∀ i,x i=c i • y i)
    (first last : Option ℕ) (xs : List (Bool × ℕ)) (s : Bool) :
    optionalCoefficient x first *
      algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) =
    (optionalCoefficient c first * ((xs.map (fun a => c a.2)).prod * optionalCoefficient c last)) •
      (optionalCoefficient y first *
        algebraPatchingWord v (xs.map (fun a => (a.1,y a.2)) ++ [(s,optionalCoefficient y last)])) := by
  have hw := algebraPatchingWord_scale v (optionalCoefficient x) (optionalCoefficient y)
    (optionalCoefficient c) (optionalCoefficient_scale x y c h)
    (xs.map (fun a => (a.1,some a.2)) ++ [(s,last)])
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_map,Function.comp_def,
    optionalCoefficient,List.prod_append,List.prod_cons,List.prod_nil,mul_one] at hw
  change algebraPatchingWord v (xs.map (fun a => (a.1,x a.2)) ++ [(s,optionalCoefficient x last)]) =
    ((xs.map (fun a => c a.2)).prod * optionalCoefficient c last) •
      algebraPatchingWord v (xs.map (fun a => (a.1,y a.2)) ++ [(s,optionalCoefficient y last)]) at hw
  rw [hw,optionalCoefficient_scale x y c h first,smul_mul_assoc,mul_smul_comm,smul_smul]

end Generator.Tracial

end

end OAI
