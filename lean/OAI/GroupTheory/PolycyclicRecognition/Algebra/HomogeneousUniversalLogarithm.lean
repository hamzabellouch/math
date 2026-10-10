import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightedWordLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.HomogeneousWordCoefficients

namespace OAI

/-! # Homogeneous Lie expansions of the universal logarithm coefficients -/

noncomputable section
namespace PolycyclicRecognition

variable {n d : ℕ}

theorem IsHomogeneousRationalWord.zero : IsHomogeneousRationalWord (0 : RationalWords n) d := by
  intro w hw
  simp at hw

theorem IsHomogeneousRationalWord.add {p q : RationalWords n}
    (hp : IsHomogeneousRationalWord p d) (hq : IsHomogeneousRationalWord q d) :
    IsHomogeneousRationalWord (p + q) d := by
  intro w hw
  by_contra hd
  have hp0 : p.coeff w = 0 := by by_contra h; exact hd (hp w h)
  have hq0 : q.coeff w = 0 := by by_contra h; exact hd (hq w h)
  exact hw (by simp [hp0, hq0])

theorem IsHomogeneousRationalWord.smul {p : RationalWords n}
    (hp : IsHomogeneousRationalWord p d) (a : ℚ) : IsHomogeneousRationalWord (a • p) d := by
  intro w hw
  by_contra hd
  have hp0 : p.coeff w = 0 := by by_contra h; exact hd (hp w h)
  exact hw (by simp [hp0])

theorem homogeneousRationalWord_single (w : FreeMonoid (Fin n)) (a : ℚ)
    (h : a ≠ 0 → w.length = d) : IsHomogeneousRationalWord (MonoidAlgebra.single w a) d := by
  classical
  intro v hv
  by_cases hw : w = v
  · subst v
    apply h
    simpa using hv
  · exact (hv (by simp [MonoidAlgebra.coeff_single, hw])).elim

theorem weightedWord_coefficient_homogeneous (c d : ℕ) (w : FreeMonoid (Fin n)) :
    IsHomogeneousRationalWord
      (monoidCoefficientLinear (truncatedScalarCoefficient c d) (weightedWord c n w)) d := by
  rw [weightedWord, monoidCoefficientLinear_single]
  apply homogeneousRationalWord_single
  intro ha
  by_contra hd
  apply ha
  by_cases hc : w.length ≤ c
  · rw [truncatedScalarCoefficient_parameter_pow c w.length d hc, ite_eq_right hd]
  · have hz : truncatedScalarParameter c ^ w.length = 0 :=
      pow_eq_zero_of_le (Nat.lt_of_not_ge hc) (truncatedScalarParameter_pow c)
    rw [hz, map_zero]

theorem weightedWordSpan_coefficient_homogeneous (c n d : ℕ) (p : TruncatedWords c n)
    (hp : p ∈ weightedWordSpan c n) :
    IsHomogeneousRationalWord (monoidCoefficientLinear (truncatedScalarCoefficient c d) p) d := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w, rfl⟩ := hp
    exact weightedWord_coefficient_homogeneous c d w
  | zero => simpa only [map_zero] using IsHomogeneousRationalWord.zero (n := n) (d := d)
  | add p q _ _ hp hq => simpa only [map_add] using hp.add hq
  | smul a p _ hp => simpa only [map_smul] using hp.smul a

theorem universalLogarithmCoefficient_homogeneous (c n d : ℕ) :
    IsHomogeneousRationalWord (universalLogarithmCoefficient c n d) d :=
  weightedWordSpan_coefficient_homogeneous c n d _ (weightedWordLogarithm_mem c n)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Each positive-degree universal logarithm coefficient is a finite Lie polynomial. -/
theorem universalLogarithmCoefficient_lie_expansion {A : Type*} [Ring A] [Algebra ℚ A]
    (c n d : ℕ) (X : Fin n → A) :
    rationalWordEvaluation X (universalLogarithmCoefficient c n (d + 1)) =
      ∑ w : Fin (d + 1) → Fin n,
        ((d + 1 : ℚ)⁻¹ * (universalLogarithmCoefficient c n (d + 1)).coeff (wordOfFn w)) •
          evalBracketWord X (rightNestedWord d w) :=
  primitive_word_finite_expansion X _ (universalLogarithmCoefficient_primitive c n (d + 1))
    (universalLogarithmCoefficient_homogeneous c n (d + 1))

end PolycyclicRecognition

end

end OAI
