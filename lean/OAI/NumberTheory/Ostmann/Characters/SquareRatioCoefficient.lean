import OAI.NumberTheory.Ostmann.Tree.CrossPairMajorant
import OAI.NumberTheory.Ostmann.Characters.SquareAverage

namespace OAI

/-! # Square-coordinate coefficients of a fixed-difference quartet -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance squareRatioFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem squareCharacterMass_inv {p : ℕ} [Fact p.Prime]
    (a : MulChar (ZMod p) ℂ → ℝ) (ρ : MulChar (ZMod p) ℂ) :
    squareCharacterMass (fun ν => a ν⁻¹) ρ = squareCharacterMass a ρ⁻¹ := by
  classical
  unfold squareCharacterMass
  simp only [Finset.sum_filter]
  have h := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp
    (fun ν => if ν ^ 2 = ρ then a ν⁻¹ else 0)
  change (∑ ν : MulChar (ZMod p) ℂ, if ν⁻¹ ^ 2 = ρ then a (ν⁻¹)⁻¹ else 0) = _ at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro ν _
  simp only [inv_inv, inv_pow, inv_eq_iff_eq_inv]

theorem ratioTest_mellinCoefficient {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (ν : MulChar (ZMod p) ℂ) :
    mellinCoefficient (ratioTest F y) ν =
      ((p : ℂ) / (Fintype.card (ZMod p)ˣ : ℂ)) *
        ratioDifferenceTransform F y ν⁻¹ := by
  have h := ratioDifferenceTransform_eq_mellin F y h0 hy ν⁻¹
  rw [inv_inv] at h
  rw [h]
  have hp : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hU : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The square-root ambiguity of a moving leaf costs exactly the square-fiber
factor two. The ratio-to-difference normalization is explicit. -/
theorem ratioTest_square_mellin_bound {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun z => ratioTest F y (K * z ^ 2)) ρ‖ ^ 2 ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ⁻¹ := by
  classical
  have h := mellinCoefficient_square_pullback_bound Finset.univ
    (mellinCoefficient (ratioTest F y)) (ratioTest F y)
    (fun z => (mellin_inversion _ z).symm) K ρ
  simp_rw [ratioTest_mellinCoefficient F y h0 hy, norm_mul, norm_div,
    Complex.norm_natCast, mul_pow] at h
  have he : (∑ ν ∈ Finset.univ.filter (fun ν : MulChar (ZMod p) ℂ => ν ^ 2 = ρ),
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        ‖ratioDifferenceTransform F y ν⁻¹‖ ^ 2) =
      ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ⁻¹ := by
    rw [← Finset.mul_sum]
    congr 1
    change squareCharacterMass (fun ν => ‖ratioDifferenceTransform F y ν⁻¹‖ ^ 2) ρ = _
    exact squareCharacterMass_inv (fun ν => ‖ratioDifferenceTransform F y ν‖ ^ 2) ρ
  rw [he] at h
  exact h.trans_eq (by ring)

noncomputable def quartetRatioValue {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (z t r : (ZMod p)ˣ) : ℂ :=
  ratioTest (fun d =>
    fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))) y r

theorem quartetRatioValue_at_difference {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y d e z t : (ZMod p)ˣ)
    (hdiff : (d : ZMod p) - e = y) :
    quartetRatioValue g h left right y z t (d / e) =
      fieldBottomPairValue g d (quartetLeftRatio left z d e) *
        fieldBottomPairValue h e (quartetRightRatio right t d e) := by
  have hde : (d : ZMod p) ≠ e := by
    intro he
    have hz : (y : ZMod p) = 0 := by rw [← hdiff, he, sub_self]
    exact Units.ne_zero y hz
  have ht : d / e ≠ 1 := by
    intro hh
    apply hde
    exact Units.ext_iff.mp (div_eq_one.mp hh)
  have hc := pair_coordinates_reconstruct (d : ZMod p) e (Units.ne_zero e) hde
  have hx : (y : ZMod p) * ((d / e : (ZMod p)ˣ) : ZMod p) /
      (((d / e : (ZMod p)ˣ) : ZMod p) - 1) = d := by
    rw [← hdiff, Units.val_div_eq_div_val]
    exact congrArg Prod.fst hc
  simp only [quartetRatioValue, ratioTest, ht, ite_false, hx, sub_eq_iff_eq_add.mpr
    (show (d : ZMod p) = (e : ZMod p) + y by linear_combination hdiff)]

theorem quartetRatioValue_square_mellin_bound {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ)
    (z t K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun r => quartetRatioValue g h left right y z t (K * r ^ 2)) ρ‖ ^ 2 ≤
      2 * ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 *
        squareCharacterMass (fun ν => ‖quartetParameterValue g h left right ν y z t‖ ^ 2) ρ⁻¹ := by
  exact ratioTest_square_mellin_bound _ y (by simp) (by simp) K ρ

end Ostmann

end OAI
