import OAI.Analysis.CircleDomains.Rigidity.SmoothTraceTruncation
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The truncations converge pointwise, and their derivatives converge
away from zero while remaining zero at zero. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem smoothTraceTruncation_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => smoothTraceTruncation (δ n) t) atTop (𝓝 t) := by
  by_cases hz : t = 0
  · subst t
    have he : (fun n => smoothTraceTruncation (δ n) 0) = fun _ => (0 : ℝ) := by
      funext n
      exact smoothTraceTruncation_zero (hδ n) (hδ n).le
    rw [he]
    exact tendsto_const_nhds
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hl2 : Tendsto (fun n => 2 * δ n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hl.const_mul 2
    have hev : ∀ᶠ n in atTop, 2 * δ n < t := hl2.eventually (gt_mem_nhds hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (smoothTraceTruncation_eq_self (hδ n) hn.le).symm

 theorem smoothTraceTruncation_deriv_tendsto {δ : ℕ → ℝ}
    (hδ : ∀ n, 0 < δ n) (hl : Tendsto δ atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => deriv (smoothTraceTruncation (δ n)) t) atTop
      (𝓝 (if t = 0 then 0 else 1)) := by
  split_ifs with hz
  · subst t
    have he : (fun n => deriv (smoothTraceTruncation (δ n)) 0) = fun _ => (0 : ℝ) := by
      funext n
      exact smoothTraceTruncation_deriv_zero (hδ n) (hδ n).le
    rw [he]
    exact tendsto_const_nhds
  · have hp : 0 < t := lt_of_le_of_ne ht (Ne.symm hz)
    have hl2 : Tendsto (fun n => 2 * δ n) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hl.const_mul 2
    have hev : ∀ᶠ n in atTop, 2 * δ n < t := hl2.eventually (gt_mem_nhds hp)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with n hn
    exact (smoothTraceTruncation_deriv_one (hδ n) hn.le).symm

end CircleDomainRigidity

end

end OAI
