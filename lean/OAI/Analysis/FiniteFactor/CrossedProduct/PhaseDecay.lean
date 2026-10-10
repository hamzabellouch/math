import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseCount
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- An explicit majorant for the positive-power union bound. -/
def sourcePhaseFailureMajorant (s : ℕ) : ℝ :=
  (sourceBlockSize s : ℝ)^((4/5 : ℝ)*(sourceBlockSize s : ℝ)) *
    2^sourceBlockSize s * (10*sourceWidth s 1)^sourceMissCount s

theorem phaseFailureMajorant_le (m q : ℕ) (hm : (100 : ℝ) ≤ m)
    (hroot : (10 : ℝ) ≤ (m : ℝ)^(1/100 : ℝ))
    (hq : (19/20 : ℝ)*(m : ℝ) ≤ q) :
    (m : ℝ)^((4/5 : ℝ)*(m : ℝ))*2^m*
      (10*(m : ℝ)^(-19/20 : ℝ))^q ≤ (m : ℝ)^(-2 : ℝ) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hb : 10*(m : ℝ)^(-19/20 : ℝ) ≤ (m : ℝ)^(-47/50 : ℝ) := by
    calc
      _ ≤ (m : ℝ)^(1/100 : ℝ)*(m : ℝ)^(-19/20 : ℝ) := by gcongr
      _ = _ := by rw [← Real.rpow_add hm0]; norm_num
  have htwo : (2 : ℝ)^m ≤ ((m : ℝ)^(1/100 : ℝ))^m := by
    gcongr
    linarith
  calc
    _ ≤ (m : ℝ)^((4/5 : ℝ)*(m : ℝ))*((m : ℝ)^(1/100 : ℝ))^m*
        ((m : ℝ)^(-47/50 : ℝ))^q := by gcongr
    _ = (m : ℝ)^((4/5 : ℝ)*(m : ℝ)+(1/100 : ℝ)*(m : ℝ)+(-47/50 : ℝ)*(q : ℝ)) := by
      rw [← Real.rpow_mul_natCast hm0.le, ← Real.rpow_mul_natCast hm0.le,
        ← Real.rpow_add hm0, ← Real.rpow_add hm0]
    _ ≤ (m : ℝ)^(-2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hm1
      nlinarith

theorem sourceBlockSize_tendsto : Tendsto sourceBlockSize atTop atTop := by
  have hs : StrictMono (fun s => (sourceStageState s).K) := by
    apply strictMono_nat_of_lt_succ
    intro s
    have hh := sourceStage_cutoff_growth s
    omega
  exact tendsto_atTop_mono (fun s => (sourceStage s).m_ge_K) hs.tendsto_atTop

theorem sourcePhaseFailureMajorant_eventually :
    ∀ᶠ s in atTop, sourcePhaseFailureMajorant s ≤ (sourceBlockSize s : ℝ)^(-2 : ℝ) := by
  have ht : Tendsto (fun s => (sourceBlockSize s : ℝ)^(1/100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp
      (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  filter_upwards [ht.eventually (eventually_ge_atTop 10)] with s hs
  exact phaseFailureMajorant_le (sourceBlockSize s) (sourceMissCount s)
    (by exact_mod_cast (sourceStage s).m_ge_100) hs (Nat.le_ceil _)

/-- The reciprocal-square majorant is summable from m_s >= 2^(s+1). -/
theorem sourceBlockSize_inverseSquare_summable :
    Summable (fun s => (sourceBlockSize s : ℝ)^(-2 : ℝ)) := by
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).of_nonneg_of_le
  · intro s; positivity
  · intro s
    have hm1 : (1 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (show 1 ≤ sourceBlockSize s by change 1 ≤ (sourceStage s).m; have := (sourceStage s).m_ge_100; omega)
    have hp : (2 : ℝ)^s ≤ sourceBlockSize s := by
      have hh := (sourceStage s).m_ge_pow
      have hh' : 2^s ≤ sourceBlockSize s := by change 2^(s+1) ≤ sourceBlockSize s at hh; have := Nat.le_mul_of_pos_right (2^s) (by omega : 0 < 2); rw [pow_succ] at hh; omega
      exact_mod_cast hh'
    calc
      _ ≤ (sourceBlockSize s : ℝ)^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
      _ = 1/(sourceBlockSize s : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ ≤ 1/(2 : ℝ)^s := one_div_le_one_div_of_le (by positivity) hp
      _ = (1/2 : ℝ)^s := by rw [one_div_pow]

theorem sourcePhaseFailureMajorant_summable : Summable sourcePhaseFailureMajorant := by
  apply sourceBlockSize_inverseSquare_summable.of_norm_bounded_eventually_nat
  filter_upwards [sourcePhaseFailureMajorant_eventually] with s hs
  rwa [Real.norm_eq_abs, abs_of_nonneg (by unfold sourcePhaseFailureMajorant sourceWidth; dsimp; positivity)]

end
end FiniteFactor

end OAI
