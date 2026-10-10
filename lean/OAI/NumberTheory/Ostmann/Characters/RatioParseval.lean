import OAI.NumberTheory.Ostmann.ZeroDensity.PairDensity

namespace OAI

/-! # Parseval in the ratio of two nonzero arguments with fixed difference -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance ratioParsevalFintype {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable def ratioTest {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (t : (ZMod p)ˣ) : ℂ :=
  if t = 1 then 0 else F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))

noncomputable def ratioDifferenceTransform {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (ν : MulChar (ZMod p) ℂ) : ℂ :=
  (p : ℂ)⁻¹ * ∑ d : ZMod p, F d * ν (d / (d - y))

theorem ratioTest_sum {p : ℕ} [Fact p.Prime]
    {R : Type*} [AddCommMonoid R] (F : ZMod p → R)
    (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0) :
    (∑ t : (ZMod p)ˣ, if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))) = ∑ d : ZMod p, F d := by
  let e : ZMod p ≃ ZMod p :=
    (Function.Involutive.toPerm _ ratioInvolution_involutive).trans
      (Equiv.mulLeft₀ (y : ZMod p) (Units.ne_zero y))
  have he (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))) = F (e t) := by
    by_cases ht : t = 1
    · simp [ht, e, ratioInvolution, hy]
    · have ht' : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      simp [ht, ht', e, ratioInvolution, mul_div_assoc]
  simp_rw [he]
  have he0 : F (e 0) = 0 := by simp [e, ratioInvolution, h0]
  rw [sum_units_eq_sum_of_zero (fun t => F (e t)) he0]
  exact e.sum_comp F

theorem ratioDifferenceTransform_eq_mellin {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0)
    (ν : MulChar (ZMod p) ℂ) :
    ratioDifferenceTransform F y ν =
      ((Fintype.card (ZMod p)ˣ : ℂ) / (p : ℂ)) *
        mellinCoefficient (ratioTest F y) ν⁻¹ := by
  have hsum := ratioTest_sum (fun d => F d * ν (d / (d - y))) y
    (by simp [h0]) (by simp [hy])
  have hterm (t : (ZMod p)ˣ) : (if t = 1 then 0 else
      F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) *
        ν (((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) /
          ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y))) =
      ratioTest F y t * conj (ν⁻¹ t) := by
    by_cases ht : t = 1
    · simp [ht, ratioTest]
    · have ht' : (t : ZMod p) ≠ 1 := fun h => ht (Units.ext h)
      have hden : (t : ZMod p) - 1 ≠ 0 := sub_ne_zero.mpr ht'
      have he : ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1)) /
          ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y) = t := by
        have hd := pair_coordinate_difference (y : ZMod p) (t : ZMod p) ht'
        rw [show (y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1) - y =
          (y : ZMod p) / ((t : ZMod p) - 1) by linear_combination hd]
        field_simp
      have hn : conj (ν⁻¹ t) = ν t := by
        rw [MulChar.inv_apply_eq_inv', Complex.inv_eq_conj (norm_mulChar_unit ν t)]
        simp
      simp only [ht, ite_false, ratioTest, he, hn]
  simp_rw [hterm] at hsum
  unfold ratioDifferenceTransform mellinCoefficient
  rw [← hsum]
  have hU : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The sum over all quotient characters costs no small-correlation hypothesis. -/
theorem ratioDifferenceTransform_parseval {p : ℕ} [Fact p.Prime]
    (F : ZMod p → ℂ) (y : (ZMod p)ˣ) (h0 : F 0 = 0) (hy : F y = 0) :
    (∑ ν : MulChar (ZMod p) ℂ, ‖ratioDifferenceTransform F y ν‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ) / (p : ℝ) ^ 2 * ∑ d : ZMod p, ‖F d‖ ^ 2 := by
  simp_rw [ratioDifferenceTransform_eq_mellin F y h0 hy, norm_mul, norm_div,
    Complex.norm_natCast, mul_pow]
  rw [← Finset.mul_sum]
  have hinv := (Equiv.inv (MulChar (ZMod p) ℂ)).bijective.sum_comp
    (fun ν => ‖mellinCoefficient (ratioTest F y) ν‖ ^ 2)
  change (∑ ν : MulChar (ZMod p) ℂ, ‖mellinCoefficient (ratioTest F y) ν⁻¹‖ ^ 2) =
    ∑ ν : MulChar (ZMod p) ℂ, ‖mellinCoefficient (ratioTest F y) ν‖ ^ 2 at hinv
  rw [hinv, mellin_parseval]
  have hsum := ratioTest_sum (fun d => ‖F d‖ ^ 2) y (by simp [h0]) (by simp [hy])
  have hnorm (t : (ZMod p)ˣ) : ‖ratioTest F y t‖ ^ 2 =
      if t = 1 then 0 else ‖F ((y : ZMod p) * (t : ZMod p) / ((t : ZMod p) - 1))‖ ^ 2 := by
    unfold ratioTest
    split_ifs <;> simp
  simp_rw [hnorm]
  rw [hsum]
  have hU : (Fintype.card (ZMod p)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

end Ostmann

end OAI
