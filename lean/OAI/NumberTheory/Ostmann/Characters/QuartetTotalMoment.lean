import OAI.NumberTheory.Ostmann.Characters.RatioParseval
import OAI.NumberTheory.Ostmann.Characters.FieldPairMoment
import OAI.NumberTheory.Ostmann.Characters.QuartetOrientations

namespace OAI

/-! # The total character mass of the cross-pair quartet coefficients -/

namespace Ostmann

open scoped BigOperators

noncomputable local instance quartetTotalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem quartetParameterValue_sum_characters {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ) (z t : (ZMod p)ˣ) :
    (∑ ν : MulChar (ZMod p) ℂ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 *
        ∑ d : ZMod p,
          ‖fieldBottomPairValue g d (quartetLeftRatio left z d (d - y))‖ ^ 2 *
          ‖fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))‖ ^ 2 := by
  have hh := ratioDifferenceTransform_parseval
    (fun d => fieldBottomPairValue g d (quartetLeftRatio left z d (d - y)) *
      fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y)))
      y (by simp) (by simp)
  simpa only [quartetParameterValue, ratioDifferenceTransform, norm_mul, mul_pow] using hh

theorem fieldPairMoment_parameter_average {p : ℕ} [Fact p.Prime]
    (g : ZMod p → ℂ) (friendly : Bool) (d e : (ZMod p)ˣ) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ,
        ‖fieldBottomPairValue g d (quartetLeftRatio friendly z d e)‖ ^ 2) =
      fieldPairMoment g d := by
  let a := if friendly then d else e⁻¹
  have he (z : (ZMod p)ˣ) : quartetLeftRatio friendly z d e = ((z * a : (ZMod p)ˣ) : ZMod p) := by
    cases friendly
    · change (z : ZMod p) / e = ((z * e⁻¹ : (ZMod p)ˣ) : ZMod p)
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
    · rfl
  simp_rw [he]
  unfold fieldPairMoment
  congr 1
  exact (Equiv.mulRight a).bijective.sum_comp (fun z => ‖fieldBottomPairValue g d z‖ ^ 2)

theorem quartet_pair_parameter_average {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (d e : ZMod p) :
    (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖fieldBottomPairValue g d (quartetLeftRatio left z d e)‖ ^ 2 *
          ‖fieldBottomPairValue h e (quartetRightRatio right t d e)‖ ^ 2) =
      fieldPairMoment g d * fieldPairMoment h e := by
  by_cases hd : d = 0
  · simp [hd]
  by_cases he : e = 0
  · simp [he]
  let D : (ZMod p)ˣ := Units.mk0 d hd
  let E : (ZMod p)ˣ := Units.mk0 e he
  have hL := fieldPairMoment_parameter_average g left D E
  have hR := fieldPairMoment_parameter_average h right E D
  change (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
        ∑ t : (ZMod p)ˣ,
          ‖fieldBottomPairValue g D (quartetLeftRatio left z D E)‖ ^ 2 *
          ‖fieldBottomPairValue h E (quartetLeftRatio right t E D)‖ ^ 2) =
      fieldPairMoment g D * fieldPairMoment h E
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [← hL, ← hR]
  ring

noncomputable def quartetParameterMoment {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) (y : ZMod p) : ℝ :=
  (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
    (∑ z : (ZMod p)ˣ, (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ *
      ∑ t : (ZMod p)ˣ, ‖quartetParameterValue g h left right ν y z t‖ ^ 2)

theorem quartetParameterMoment_nonneg {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (ν : MulChar (ZMod p) ℂ) (y : ZMod p) :
    0 ≤ quartetParameterMoment g h left right ν y := by
  unfold quartetParameterMoment
  positivity

/-- The total local mass is exactly a nonnegative difference convolution. -/
theorem sum_quartetParameterMoment {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (left right : Bool) (y : (ZMod p)ˣ) :
    (∑ ν : MulChar (ZMod p) ℂ, quartetParameterMoment g h left right ν y) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 *
        differenceMoment (fieldPairMoment g) (fieldPairMoment h) y := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  let K : ℝ := U / (p : ℝ) ^ 2
  let A (ν : MulChar (ZMod p) ℂ) (z t : (ZMod p)ˣ) :=
    ‖quartetParameterValue g h left right ν y z t‖ ^ 2
  let B (d : ZMod p) (z t : (ZMod p)ˣ) :=
    ‖fieldBottomPairValue g d (quartetLeftRatio left z d (d - y))‖ ^ 2 *
      ‖fieldBottomPairValue h (d - y) (quartetRightRatio right t d (d - y))‖ ^ 2
  change (∑ ν, U⁻¹ * ∑ z, U⁻¹ * ∑ t, A ν z t) = _
  calc
    _ = U⁻¹ * ∑ z, U⁻¹ * ∑ t, ∑ ν, A ν z t := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_comm]
    _ = U⁻¹ * ∑ z, U⁻¹ * ∑ t, K * ∑ d, B d z t := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact quartetParameterValue_sum_characters g h left right y z t
    _ = K * ∑ d, U⁻¹ * ∑ z, U⁻¹ * ∑ t, B d z t := by
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ZMod p)ˣ))
        (t := (Finset.univ : Finset (ZMod p)))]
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      exact quartet_pair_parameter_average g h left right d (d - y)

/-- Uniform bounded total mass, simultaneously for all four friendly/bad choices. -/
theorem quartetParameterMoment_total_mean_le {p : ℕ} [Fact p.Prime]
    (g h : ZMod p → ℂ) (hg : g 0 = 0) (hh : h 0 = 0)
    (heg : (∑ x : ZMod p, ‖g x‖ ^ 2) ≤ (p : ℝ))
    (heh : (∑ x : ZMod p, ‖h x‖ ^ 2) ≤ (p : ℝ)) (left right : Bool) :
    (∑ ν : MulChar (ZMod p) ℂ, (∑ y : (ZMod p)ˣ,
      quartetParameterMoment g h left right ν y) / (Fintype.card (ZMod p)ˣ : ℝ)) ≤
        ((p : ℝ) / (Fintype.card (ZMod p)ˣ : ℝ)) ^ 2 := by
  let U : ℝ := Fintype.card (ZMod p)ˣ
  have hU : 0 < U := by dsimp [U]; exact_mod_cast Fintype.card_pos
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmean := mean_differenceMajorant_le (fieldPairMoment g) (fieldPairMoment h)
    (fieldPairMoment_nonneg g) (fieldPairMoment_nonneg h)
  have hgm := fieldPairMoment_mean_le g hg heg
  have hhm := fieldPairMoment_mean_le h hh heh
  calc
    _ = (U ^ 2 / (p : ℝ) ^ 2) *
        ((∑ y : (ZMod p)ˣ,
          differenceMajorant (fieldPairMoment g) (fieldPairMoment h) y) / U) := by
      simp only [Finset.sum_div]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_div, sum_quartetParameterMoment]
      simp only [differenceMajorant, ← Finset.mul_sum]
      change _ = U ^ 2 / (p : ℝ) ^ 2 * ((U⁻¹ * _) / U)
      field_simp
    _ ≤ (U ^ 2 / (p : ℝ) ^ 2) *
        (((∑ d : ZMod p, fieldPairMoment g d) / U) *
          ((∑ d : ZMod p, fieldPairMoment h d) / U)) :=
      mul_le_mul_of_nonneg_left hmean (by positivity)
    _ ≤ (U ^ 2 / (p : ℝ) ^ 2) * (((p : ℝ) / U) ^ 2 * ((p : ℝ) / U) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul hgm hhm
        (div_nonneg (Finset.sum_nonneg fun d _ => fieldPairMoment_nonneg h d) hU.le)
        (sq_nonneg _)
    _ = _ := by dsimp [U]; field_simp

end Ostmann

end OAI
