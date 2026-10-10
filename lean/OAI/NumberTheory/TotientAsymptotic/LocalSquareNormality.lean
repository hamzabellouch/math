import OAI.NumberTheory.TotientAsymptotic.LocalSquareCutoff
import OAI.NumberTheory.TotientAsymptotic.LocalNormalityMass

namespace OAI

/-! The actual logarithmic square cutoff lies below each local normality scale. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem local_square_cutoff_le_normality {A : ℝ} (_hA : 0 ≤ A) :
    ∀ᶠ h : ℕ in atTop,∀ z : ℝ,1 < z → 0 ≤ B z →
      Real.log (B z+4) ≤ A*h →
      (localSquareCutoff z:ℝ) ≤ localNormalityScale h := by
  have hlog6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (A+Real.log 6+2)),eventually_ge_atTop (2:ℕ)] with h hh hh2
  intro z hz hB hlog
  have hh1 : (1:ℝ) ≤ h := by exact_mod_cast (show 1≤h by omega)
  have hlogh := mul_le_mul_of_nonneg_left hh1 hlog6
  have hlarge := mul_le_mul_of_nonneg_right hh (Nat.cast_nonneg (α:=ℝ) h)
  have hpow : (h:ℝ)^2 ≤ (h:ℝ)^4 := by
    have hsq : 1 ≤ (h:ℝ)^2 := one_le_pow₀ hh1
    have hm := mul_nonneg (sq_nonneg (h:ℝ)) (sub_nonneg.mpr hsq)
    nlinarith only [hm]
  have hexponent : Real.log 6+A*h ≤ (h:ℝ)^4 := by
    nlinarith only [hlogh,hlarge,hpow,Nat.cast_nonneg (α:=ℝ) h]
  have harg : 6*B z ≤ Real.exp ((h:ℝ)^4) := by
    have he := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by linarith only [hB] : 0 < B z+4)] at he
    have hm := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ)≤6)
    have hh := Real.exp_le_exp.mpr hexponent
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<6)] at hh
    linarith only [hm,hh]
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have heq : (Real.log z)^6=Real.exp (6*B z) := by
    simpa only [Nat.cast_ofNat,B,Real.exp_log hlogz] using
      (Real.exp_nat_mul (B z) 6).symm
  have hfloor : (localSquareCutoff z:ℝ) ≤ (Real.log z)^6 :=
    Nat.floor_le (pow_nonneg hlogz.le 6)
  exact hfloor.trans (heq.trans_le (Real.exp_le_exp.mpr harg))

lemma squarefreeAbove_of_local_cutoff {n h : ℕ} {z : ℝ}
    (hcut : (localSquareCutoff z:ℝ) ≤ localNormalityScale h)
    (hsq : ∀ p : ℕ,p.Prime → localSquareCutoff z<p → ¬p^2 ∣ n) :
    SquarefreeAbove n (localNormalityScale h) := by
  intro p hp hlarge
  apply hsq p hp
  exact_mod_cast hcut.trans_lt hlarge

end TotientAsymptotic

end

end OAI
