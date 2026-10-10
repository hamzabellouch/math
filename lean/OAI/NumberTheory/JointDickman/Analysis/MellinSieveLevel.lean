import OAI.NumberTheory.JointDickman.Analysis.MellinSieveBudget

namespace OAI

/-! # A small prime-sieve level with quantitative logarithmic size -/
namespace JointDickman
open Filter
open scoped Topology

lemma mellin_small_sieve_level {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop,
      2 ≤ ⌊q^κ⌋₊ ∧ (⌊q^κ⌋₊ : ℝ) ≤ q ∧
      ((⌊q^κ⌋₊+1:ℕ):ℝ) ≤ 2*q^κ ∧
      (κ/2)*Real.log q ≤ Real.log (⌊q^κ⌋₊ : ℝ) := by
  have hp := (tendsto_rpow_atTop (show 0 < κ/2 by positivity)).eventually_ge_atTop 2
  filter_upwards [eventually_gt_atTop (1:ℝ),hp] with q hq hpow
  have hq0 : 0 < q := by linarith
  have he : (q^(κ/2))^2 = q^κ := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hq0.le]
    congr 1
    ring
  have hfloor : q^(κ/2) ≤ (⌊q^κ⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (q^κ)
    nlinarith [sq_nonneg (q^(κ/2)-1)]
  have hfloor2 : 2 ≤ ⌊q^κ⌋₊ := by exact_mod_cast hpow.trans hfloor
  have hle := Nat.floor_le (Real.rpow_nonneg hq0.le κ)
  refine ⟨hfloor2, hle.trans ?_, ?_, ?_⟩
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hq.le hκ1
  · push_cast
    have hp1 : 1 ≤ q^κ := by
      rw [← he]
      nlinarith
    linarith
  · have hh := Real.log_le_log (Real.rpow_pos_of_pos hq0 _) hfloor
    rwa [Real.log_rpow hq0] at hh

lemma mellin_sieve_level_tendsto {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun q : ℝ => (⌊q^κ⌋₊ : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp (tendsto_nat_floor_atTop.comp (tendsto_rpow_atTop hκ))

end JointDickman

end OAI
