import Mathlib
import OAI.Combinatorics.RamseyFive.Probability.PencilFactor
import OAI.Combinatorics.RamseyFive.Probability.QB
import OAI.Combinatorics.RamseyFive.Decoding.Threshold

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreScalars

theorem normalized_pair_high {q n a χ E : ℝ} (hq : 1≤q) (hn : 0<n)
    (ha : 0<a) (ha2 : a≤2) (hcap : n≤q^3)
    (hexp : (34359738369*2^200:ℝ)≤Real.exp χ)
    (hgeom : E≤2*(HighParameters.degree q n a χ:ℝ)*(q+1)^2) :
    E*a^200≤(q^4/n)^2*Real.exp (2*χ) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  have hB : 0≤q^4/n := by positivity
  have hceil := Nat.ceil_lt_add_one (show 0≤34359738368*q^6/(n^2*a^4)*Real.exp χ by positivity)
  change (HighParameters.degree q n a χ:ℝ)<_ at hceil
  have hpoly := (pencil_factor hq).2
  have hb := pow_le_pow_left₀ hq0.le (q_le_B hq0 hn hcap) 2
  have hh := mul_le_mul_of_nonneg_right hgeom (pow_nonneg ha.le 200)
  have hbound : 2*(HighParameters.degree q n a χ:ℝ)*(q+1)^2*a^200 ≤
      34359738368*8*(q^4/n)^2*Real.exp χ*a^196+8*q^2*a^200 := by
    calc
      _ ≤ 2*(34359738368*q^6/(n^2*a^4)*Real.exp χ+1)*(4*q^2)*a^200 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha.le 200)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hceil.le (by norm_num)) hpoly
          (sq_nonneg (q+1)) (by positivity)
      _ = _ := by field_simp; ring
  have h1 : 1≤Real.exp χ := by linarith
  have hnoise : 8*q^2*a^200≤8*(q^4/n)^2*Real.exp χ*2^200 := by
    have hb' := hb.trans (le_mul_of_one_le_right (sq_nonneg _) h1)
    have hp := mul_le_mul hb' (pow_le_pow_left₀ ha.le ha2 200)
      (pow_nonneg ha.le 200) (by positivity : 0≤(q^4/n)^2*Real.exp χ)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤8)
  have hmain := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le ha2 196)
    (by positivity : 0≤34359738368*8*(q^4/n)^2*Real.exp χ)
  apply (hh.trans hbound).trans
  calc
    _ ≤ 34359738368*8*(q^4/n)^2*Real.exp χ*2^196+
        8*(q^4/n)^2*Real.exp χ*2^200 := add_le_add hmain hnoise
    _ ≤ (34359738369*2^200)*(q^4/n)^2*Real.exp χ := by
      have hcoef : (34359738368*8*2^196+8*2^200:ℝ)≤34359738369*2^200 := by norm_num
      calc
        _ = (34359738368*8*2^196+8*2^200)*((q^4/n)^2*Real.exp χ) := by ring
        _ ≤ (34359738369*2^200)*((q^4/n)^2*Real.exp χ) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
        _ = _ := by ring
    _ ≤ Real.exp χ*(q^4/n)^2*Real.exp χ := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by rw [show 2*χ=χ+χ by ring,Real.exp_add];ring

end SharpRamseyFive.ScoreScalars

end OAI
