import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceTypical

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

lemma higherSource_error_small {c δ C ell M Λ : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (_hC : 0 ≤ C) (he : 0 < ell)
    (hM : c ≤ M) (hΛ : ell^2 ≤ Λ) (hsmall : 4*C/(c*δ^2) < ell) :
    (M*Λ)⁻¹*(C*ell) < (δ/2)^2 := by
  have hMp : 0 < M := hc.trans_le hM
  have hΛp : 0 < Λ := (sq_pos_of_pos he).trans_le hΛ
  have hh := (div_lt_iff₀ (mul_pos hc (sq_pos_of_pos hδ))).mp hsmall
  have hh' := mul_lt_mul_of_pos_right hh he
  have hprod : c*ell^2 ≤ M*Λ := mul_le_mul hM hΛ (sq_nonneg _) hMp.le
  rw [inv_mul_eq_div]
  apply (div_lt_iff₀ (mul_pos hMp hΛp)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg δ)]

lemma higherSource_typical_loss {c t n y : ℝ}
    (hc : 0 < c) (ht : 1 ≤ t) (_hn : 0 ≤ n) (hy : 0 ≤ y)
    (hnt : n ≤ t) (hcT : 2/c ≤ t) :
    n*y/t^10 ≤ (c/2)*y/t^3 := by
  have htp : 0 < t := by linarith
  have hpow : 2/c ≤ t^6 := hcT.trans (le_self_pow₀ ht (by norm_num))
  have hh : 2 ≤ c*t^6 := by
    have hmul := (div_le_iff₀ hc).mp hpow
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hh htp.le
  have hbase : n/t^7 ≤ c/2 := by
    apply (div_le_iff₀ (pow_pos htp 7)).mpr
    rw [pow_succ]
    nlinarith
  calc
    _ = (y/t^3)*(n/t^7) := by field_simp
    _ ≤ (y/t^3)*(c/2) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring

end Ostmann.Characters

end

end OAI
