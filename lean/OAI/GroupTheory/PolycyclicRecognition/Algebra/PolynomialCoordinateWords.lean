import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialBilinearWords
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateGroup

namespace OAI

/-! # Ordered real powers in polynomial exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {I V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def coordinateProductWord (m : V → V → V) (X : I → V) : List I → (I → ℝ) → V
  | [], _ => 0
  | i :: l, t => m (t i • X i) (coordinateProductWord m X l t)

def polynomialCoordinateLine (m : V → V → V) (hm : PolynomialGroupLaws m) (v : V) :
    Multiplicative ℝ →* PolynomialCoordinateGroup m hm where
  toFun t := PolynomialCoordinateGroup.exp m hm (t.toAdd • v)
  map_one' := by
    change PolynomialCoordinateGroup.exp m hm ((0 : ℝ) • v) = 1
    rw [zero_smul, PolynomialCoordinateGroup.exp_zero]
  map_mul' s t := by
    exact PolynomialCoordinateGroup.exp_add_smul m hm v s.toAdd t.toAdd

theorem polynomialCoordinate_exp_zpow (m : V → V → V) (hm : PolynomialGroupLaws m)
    (v : V) (n : ℤ) :
    (PolynomialCoordinateGroup.exp m hm v) ^ n =
      PolynomialCoordinateGroup.exp m hm ((n : ℝ) • v) := by
  let f := polynomialCoordinateLine m hm v
  have h1 : f (Multiplicative.ofAdd 1) = PolynomialCoordinateGroup.exp m hm v := by
    change PolynomialCoordinateGroup.exp m hm ((1 : ℝ) • v) = _
    rw [one_smul]
  rw [← h1, ← map_zpow]
  change PolynomialCoordinateGroup.exp m hm ((n • (1 : ℝ)) • v) = _
  rw [zsmul_eq_mul, mul_one]

theorem coordinateProductWord_integer (m : V → V → V) (hm : PolynomialGroupLaws m)
    (X : I → V) (l : List I) (z : I → ℤ) :
    PolynomialCoordinateGroup.exp m hm (coordinateProductWord m X l (fun i => (z i : ℝ))) =
      (l.map (fun i => (PolynomialCoordinateGroup.exp m hm (X i)) ^ (z i))).prod := by
  induction l with
  | nil => exact PolynomialCoordinateGroup.exp_zero m hm
  | cons i l ih =>
    change PolynomialCoordinateGroup.exp m hm
      (m ((z i : ℝ) • X i) (coordinateProductWord m X l (fun i => (z i : ℝ)))) = _
    rw [PolynomialCoordinateGroup.exp_mul, ← polynomialCoordinate_exp_zpow, ih]
    rfl

theorem coordinatePolynomial_coordinateProductWord {k d c : ℕ}
    (a : DynkinCoefficients c 2)
    (B : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))
    (X : Fin k → (Fin d → ℝ)) (l : List (Fin k)) :
    IsCoordinatePolynomial (coordinateProductWord (dynkinProduct a B) X l) := by
  induction l with
  | nil => exact IsCoordinatePolynomial.const 0
  | cons i l ih =>
    change IsCoordinatePolynomial (fun t : Fin k → ℝ =>
      dynkinProduct a B (t i • X i) (coordinateProductWord (dynkinProduct a B) X l t))
    have hp : IsCoordinatePolynomial (fun t : Fin k → ℝ =>
        Sum.elim (t i • X i) (coordinateProductWord (dynkinProduct a B) X l t)) :=
      (IsCoordinatePolynomial.coordinate_smul i (X i)).pair ih
    have hh := (coordinatePolynomial_dynkinProduct a B).comp hp
    simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr] using hh

end PolycyclicRecognition

end

end OAI
