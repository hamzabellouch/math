import OAI.Analysis.KadisonKastler.TracialConjugationBound

namespace OAI

/-! # Common right actions in a cyclic representation

Two operators in the same commutant are equal if they agree on the cyclic
vector. Equality of the right actions obtained this way makes the product
of the two tracial conjugations commute with both module actions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Conjugating a linear operator by a conjugate-linear isometry gives
a complex-linear operator. -/
def conjugationOperator (J : H ≃ₗᵢ⋆[ℂ] H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  (J : H →L⋆[ℂ] H).comp (a.comp (J : H →L⋆[ℂ] H))

@[simp]
theorem conjugationOperator_apply (J : H ≃ₗᵢ⋆[ℂ] H) (a : H →L[ℂ] H) (ξ : H) :
    conjugationOperator J a ξ = J (a (J ξ)) := rfl

theorem conjugationOperator_twice (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (a : H →L[ℂ] H) :
    conjugationOperator J (conjugationOperator J a) = a := by
  ext ξ
  change J (J (a (J (J ξ)))) = a ξ
  rw [hJ ξ, hJ (a ξ)]

/-- Equality of the right conjugates intertwines the product of the two
conjugations with the original operator. -/
theorem conjugations_comp_apply_commute
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) (ξ : H) :
    J₂ (J₁ (a ξ)) = a (J₂ (J₁ ξ)) := by
  have h := congrArg (fun b : H →L[ℂ] H => J₂ (b (J₁ ξ))) ha
  change J₂ (J₁ (a (J₁ (J₁ ξ)))) = J₂ (J₂ (a (J₂ (J₁ ξ)))) at h
  rw [hJ₁ ξ, hJ₂ (a (J₂ (J₁ ξ)))] at h
  exact h

/-- Subtracting the identity retains this commutation relation. -/
theorem tracialConjugationDefect_commute_of_common_right
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) :
    Commute (tracialConjugationDefect J₁ J₂) a := by
  change tracialConjugationDefect J₁ J₂ * a = a * tracialConjugationDefect J₁ J₂
  ext ξ
  change J₂ (J₁ (a ξ)) - a ξ = a (J₂ (J₁ ξ) - ξ)
  rw [map_sub, conjugations_comp_apply_commute J₁ J₂ hJ₁ hJ₂ a ha]

/-- The same comparison commutes with the common right operator too. -/
theorem tracialConjugationDefect_commute_both
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (ha : conjugationOperator J₁ a = conjugationOperator J₂ a) :
    Commute (tracialConjugationDefect J₁ J₂) a ∧
      Commute (tracialConjugationDefect J₁ J₂) (conjugationOperator J₁ a) := by
  refine ⟨tracialConjugationDefect_commute_of_common_right J₁ J₂ hJ₁ hJ₂ a ha, ?_⟩
  apply tracialConjugationDefect_commute_of_common_right J₁ J₂ hJ₁ hJ₂
  calc
    conjugationOperator J₁ (conjugationOperator J₁ a) = a :=
      conjugationOperator_twice J₁ hJ₁ a
    _ = conjugationOperator J₂ (conjugationOperator J₁ a) := by
      rw [ha, conjugationOperator_twice J₂ hJ₂]

/-- A cyclic vector separates the commutant, expressed without introducing
any representation or standard-form hypothesis. -/
theorem operator_eq_of_commute_of_eq_on_cyclicVector
    {I : Type*} (A : I → H →L[ℂ] H) (Ω : H)
    (hcyclic : DenseRange (fun i => A i Ω)) (q r : H →L[ℂ] H)
    (hq : ∀ i, Commute q (A i)) (hr : ∀ i, Commute r (A i))
    (hΩ : q Ω = r Ω) : q = r := by
  have he : (fun ξ => q ξ) = fun ξ => r ξ :=
    hcyclic.equalizer q.continuous r.continuous (by
      funext i
      change q (A i Ω) = r (A i Ω)
      calc
        q (A i Ω) = A i (q Ω) := congrArg (fun b : H →L[ℂ] H => b Ω) (hq i).eq
        _ = A i (r Ω) := by rw [hΩ]
        _ = r (A i Ω) := (congrArg (fun b : H →L[ℂ] H => b Ω) (hr i).eq).symm)
  ext ξ
  exact congrFun he ξ

variable [CompleteSpace H]

/-- The standard tracial conjugation turns a left multiplier into the
right multiplier by its adjoint, first on the dense algebra vectors. -/
theorem conjugationOperator_algebraVector
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hJ : ∀ x : Algebra M, J (x.val Ω) = (star x).val Ω)
    (a x : Algebra M) :
    conjugationOperator J a.val (x.val Ω) = (x * star a).val Ω := by
  rw [conjugationOperator_apply, hJ]
  change J ((a * star x).val Ω) = (x * star a).val Ω
  rw [hJ, star_mul, star_star]

/-- In a cyclic standard tracial representation the conjugated left
multiplier lies in the commutant of the whole algebra. -/
theorem conjugationOperator_mem_commutant
    (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hJ : ∀ x : Algebra M, J (x.val Ω) = (star x).val Ω)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω)) (a : Algebra M) :
    conjugationOperator J a.val ∈ M.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  let bM : Algebra M := ⟨b, hb⟩
  have he : (fun ξ => (b * conjugationOperator J a.val) ξ) =
      fun ξ => (conjugationOperator J a.val * b) ξ :=
    hcyclic.equalizer (b * conjugationOperator J a.val).continuous
      (conjugationOperator J a.val * b).continuous (by
        funext x
        change b (conjugationOperator J a.val (x.val Ω)) =
          conjugationOperator J a.val (b (x.val Ω))
        rw [conjugationOperator_algebraVector M J Ω hJ]
        change (bM * (x * star a)).val Ω =
          conjugationOperator J a.val ((bM * x).val Ω)
        rw [conjugationOperator_algebraVector M J Ω hJ, mul_assoc])
  ext ξ
  exact congrFun he ξ

/-- A common left multiplier has the same right-action value on the
common standard vector, before equality of the right operators is known. -/
theorem conjugationOperator_common_vector
    (M N : VonNeumannAlgebra H) (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (a : H →L[ℂ] H) (haM : a ∈ M) (haN : a ∈ N) :
    conjugationOperator J₁ a Ω = conjugationOperator J₂ a Ω := by
  have h₁ : J₁ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hM 1
  have h₂ : J₂ Ω = Ω := by
    simpa only [star_one, OneMemClass.coe_one, one_apply_eq_self] using hN 1
  change J₁ (a (J₁ Ω)) = J₂ (a (J₂ Ω))
  rw [h₁, h₂]
  exact (hM ⟨a, haM⟩).trans (hN ⟨a, haN⟩).symm

/-- Concrete commutant members agreeing on a cyclic vector are equal. -/
theorem operator_eq_of_mem_commutant_of_eq_on_cyclicVector
    (M : VonNeumannAlgebra H) (Ω : H)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω))
    (q r : H →L[ℂ] H) (hq : q ∈ M.commutant) (hr : r ∈ M.commutant)
    (hΩ : q Ω = r Ω) : q = r := by
  apply operator_eq_of_commute_of_eq_on_cyclicVector
    (fun x : Algebra M => x.val) Ω hcyclic q r
  · intro x
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hq x.val x.property).symm
  · intro x
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hr x.val x.property).symm
  · exact hΩ

/-- Common commutant membership and the common cyclic-vector value supply
the two commutation premises in the tracial-conjugation bound. -/
theorem tracialConjugationDefect_commute_both_of_cyclic
    (M : VonNeumannAlgebra H) (Ω : H)
    (hcyclic : DenseRange (fun x : Algebra M => x.val Ω))
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (a : H →L[ℂ] H)
    (h₁ : conjugationOperator J₁ a ∈ M.commutant)
    (h₂ : conjugationOperator J₂ a ∈ M.commutant)
    (hΩ : conjugationOperator J₁ a Ω = conjugationOperator J₂ a Ω) :
    Commute (tracialConjugationDefect J₁ J₂) a ∧
      Commute (tracialConjugationDefect J₁ J₂) (conjugationOperator J₁ a) := by
  apply tracialConjugationDefect_commute_both J₁ J₂ hJ₁ hJ₂ a
  exact operator_eq_of_mem_commutant_of_eq_on_cyclicVector M Ω hcyclic _ _ h₁ h₂ hΩ

end

end KadisonKastler

end OAI
