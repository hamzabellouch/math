import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

/-! # Polynomial prefactors disappear in the logarithmic small-noise limit -/

open Set Filter
open scoped Topology
namespace RegularPointCoordinates

theorem small_noise_log_scale {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k)
    (hε0 : Tendsto ε atTop (𝓝 0)) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun k => ε k*Real.log (ε k*a)) atTop (𝓝 0) := by
  have he : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε0,Eventually.of_forall hε⟩
  have hl : Tendsto (fun k => ε k*Real.log (ε k)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_comm,Function.comp_def] using
      (tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one).comp he
  have hh := hl.add (hε0.mul_const (Real.log a))
  simp only [zero_mul,add_zero] at hh
  convert hh using 1
  funext k
  rw [Real.log_mul (hε k).ne' ha.ne']
  ring

end RegularPointCoordinates

end OAI
