import OAI.MeasureTheory.Falconer.Incidence.OriginalPencilEqualization
import OAI.MeasureTheory.Falconer.Incidence.IncidenceScaleChoice

namespace OAI

/-! The pencil-cardinality pigeonhole has only a linear cost in the chosen
block depth, with a fixed additive cost depending on the block width. -/
namespace Falconer

theorem incidence_bucket_count_bound {δ : ℝ} (hδ : 0 < δ) (N B : ℕ)
    (hscale : 1 ≤ 4*(2:ℝ)^(N+B)*δ) :
    Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 ≤ 2*N+2*B+11 := by
  have hpow : 1 ≤ (2:ℝ)^(N+B) := one_le_pow₀ (by norm_num)
  have hdiv : 4/δ ≤ 16*(2:ℝ)^(N+B) := by
    apply (div_le_iff₀ hδ).2
    nlinarith only [hscale]
  have hbase : 4/δ+1 ≤ 32*(2:ℝ)^(N+B) := by linarith only [hdiv,hpow]
  have hsq : (4/δ+1)^2 ≤ (2:ℝ)^(2*N+2*B+10) := by
    calc
      _ ≤ (32*(2:ℝ)^(N+B))^2 := pow_le_pow_left₀ (by positivity) hbase 2
      _ = _ := by
        rw [mul_pow,← pow_mul]
        rw [show 2*N+2*B+10 = (N+B)*2+10 by omega,pow_add]
        norm_num
        ring
  have hceil : Nat.ceil ((4/δ+1)^2) ≤ 2^(2*N+2*B+10) := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsq
  have hh := Nat.log_mono_right (b := 2) hceil
  rw [Nat.log_pow (by norm_num)] at hh
  omega

theorem incidence_packing_factor_bound {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (B : ℕ) (hscale : ρ ≤ 4*(2:ℝ)^B*δ) :
    (16*ρ/δ+1)^2 ≤ (64*(2:ℝ)^B+1)^2 := by
  apply pow_le_pow_left₀ (by positivity)
  have hh := mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 16)
  have hh' := div_le_div_of_nonneg_right hh hδ.le
  have he : 16*(4*(2:ℝ)^B*δ)/δ = 64*(2:ℝ)^B := by field_simp; ring
  rw [he] at hh'
  linarith only [hh']

end Falconer

end OAI
