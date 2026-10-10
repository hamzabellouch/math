import OAI.NumberTheory.CubicMoment.Estimates.LongPrimeParameterScale
import OAI.NumberTheory.CubicMoment.Estimates.NarrowPrimeBinCount
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedRoughness

namespace OAI

/-! The actual complementary norm and exclusion bounds needed to put
stopped prime rows on the parameter log X/4. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_complement_power_bound {X C ξ P b : ℝ} {m : ℕ}
    (hX : 1 < X) (hgap : C < ξ*m) (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P) :
    b/P < (X^ξ)^m := by
  calc
    b/P ≤ b := div_le_self hb hP
    _ ≤ X^C := hbX
    _ < X^(ξ*m) := Real.rpow_lt_rpow_of_exponent_lt hX hgap
    _ = (X^ξ)^m := by rw [←Real.rpow_mul_natCast (zero_lt_one.trans hX).le]

lemma stopped_complement_exclusion_log {r d e : Eisenstein} (hr : primary r)
    (hd : primary d) (he : e ≠ 0) {X C E b P : ℝ} (hX : 0 < X)
    (hb : 0 ≤ b) (hbX : b ≤ X^C) (hP : 1 ≤ P)
    (hrd : norm (r*d) ≤ b/P) (heX : norm e ≤ X^E) :
    Real.log (norm (r*(d*e))) ≤ (C+E)*Real.log X := by
  have hrp : 0 < norm (r*d) := zero_lt_one.trans_le
    (one_le_norm (primary_ne_zero (primary_mul hr hd)))
  have hep : 0 < norm e := zero_lt_one.trans_le (one_le_norm he)
  have hrX : norm (r*d) ≤ X^C := hrd.trans ((div_le_self hb hP).trans hbX)
  calc
    Real.log (norm (r*(d*e))) = Real.log (norm (r*d))+Real.log (norm e) := by
      rw [←mul_assoc,norm_mul_eq,Real.log_mul (ne_of_gt hrp) (ne_of_gt hep)]
    _ ≤ Real.log (X^C)+Real.log (X^E) :=
      add_le_add (Real.log_le_log hrp hrX) (Real.log_le_log hep heX)
    _ = (C+E)*Real.log X := by rw [Real.log_rpow hX,Real.log_rpow hX]; ring

lemma geometricBinCount_logarithmic_width {X B δ C H : ℝ}
    (hX : 0 < X) (hL : 1 ≤ Real.log X) (hB : 1 ≤ B) (hBX : B ≤ X^C)
    (hC : 0 ≤ C) (hH : 0 ≤ H) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hwidth : (Real.log X)^(-H) ≤ δ) :
    (geometricBinCount (1+δ) B:ℝ) ≤ (2*C+1)*(Real.log X)^(H+1) := by
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL
  have hlogB : Real.log B ≤ C*Real.log X := by
    have he := Real.log_le_log (zero_lt_one.trans_le hB) hBX
    rwa [Real.log_rpow hX] at he
  have hinv : δ⁻¹ ≤ (Real.log X)^H := by
    have hi := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLp (-H)) hwidth
    simpa only [one_div,Real.rpow_neg hLp.le,inv_inv] using hi
  have hone : 1 ≤ (Real.log X)^(H+1) := Real.one_le_rpow hL (by linarith)
  apply (geometricBinCount_width_bound hδ hδone hB).trans
  calc
    2*Real.log B/δ+1 ≤ (2*(C*Real.log X))*(Real.log X)^H+1 := by
      rw [div_eq_mul_inv]
      gcongr
    _ = 2*C*(Real.log X)^(H+1)+1 := by
      rw [Real.rpow_add hLp,Real.rpow_one]
      ring
    _ ≤ (2*C+1)*(Real.log X)^(H+1) := by nlinarith

end CubicFirstMoment

end

end OAI
