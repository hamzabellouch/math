import OAI.NumberTheory.Ostmann.Characters.QuartetExpansion

namespace OAI

/-!
# The four quartet orientation formulas

A friendly side uses its own difference, and a bad side uses the reciprocal
of the other difference. The twists below are exactly the four rows in
`tree-twisted-convolution`.
-/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetOrientationsFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def quartetLeftRatio {p : ℕ} [Fact p.Prime] (friendly : Bool) (z d e : ZMod p) : ZMod p :=
  if friendly then z * d else z / e

noncomputable def quartetRightRatio {p : ℕ} [Fact p.Prime] (friendly : Bool) (t d e : ZMod p) : ZMod p :=
  if friendly then t * e else t / d

noncomputable def quartetLeftTwist {p : ℕ} [Fact p.Prime] (left right : Bool)
    (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν * (if left then χ else 1) * (if right then 1 else ψ⁻¹)

noncomputable def quartetRightTwist {p : ℕ} [Fact p.Prime] (left right : Bool)
    (ν χ ψ : MulChar (ZMod p) ℂ) : MulChar (ZMod p) ℂ :=
  ν⁻¹ * (if left then 1 else χ⁻¹) * (if right then ψ else 1)

noncomputable def quartetParameterValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p,
    fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y)) *
        ν (d / (d - y))

theorem quartetParameterValue_eq_synthesis {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ)
    (y : ZMod p) (z t : (ZMod p)ˣ) :
    quartetParameterValue g h left right ν y z t =
      quartetSynthesis (pairAutocorrelation g) (pairAutocorrelation h)
        (quartetLeftTwist left right ν) (quartetRightTwist left right ν) y z t := by
  classical
  unfold quartetParameterValue quartetSynthesis additiveDifferenceConvolution
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (MulChar (ZMod p) ℂ)))
    (t := (Finset.univ : Finset (ZMod p)))]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : d = 0
  · simp [hd, fieldBottomPairValue, quartetLeftTwist, MulChar.map_zero]
  by_cases he : d - y = 0
  · simp [he, fieldBottomPairValue, quartetRightTwist, MulChar.map_zero]
  rw [fieldBottomPairValue_expansion g d _ hd,
    fieldBottomPairValue_expansion h (d - y) _ he]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ _
  apply Finset.sum_congr rfl
  intro ψ _
  cases left <;> cases right <;>
    simp only [quartetLeftRatio, quartetRightRatio, quartetLeftTwist, quartetRightTwist,
      Bool.false_eq_true, ite_false, ite_true, mul_one,
      div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.coeToFun_mul, Pi.mul_apply] <;> ring

/-- All orientation choices have precisely the two-twist Fourier norm. -/
theorem quartetParameterValue_parseval {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) :
    (p : ℝ)⁻¹ * (∑ y : ZMod p,
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * (∑ z : (ZMod p)ˣ,
        (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
          ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2)) =
      ∑ χ : MulChar (ZMod p) ℂ, ∑ ψ : MulChar (ZMod p) ℂ, ∑ a : ZMod p,
        ‖additiveFourier (fun d => pairAutocorrelation g χ d *
          quartetLeftTwist left right ν χ ψ d) a‖ ^ 2 *
        ‖additiveFourier (fun e => pairAutocorrelation h ψ e *
          quartetRightTwist left right ν χ ψ e) (-a)‖ ^ 2 := by
  simp_rw [quartetParameterValue_eq_synthesis]
  exact quartetSynthesis_parseval _ _ _ _

end Ostmann

end OAI
