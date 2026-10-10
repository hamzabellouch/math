import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.ScalarFamily

namespace OAI


noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

lemma contDiff_scalar_family_deriv {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun p:ℝ×ℝ=>deriv (fun s=>Φ (p.1,s)) p.2) := by
  have heq (p:ℝ×ℝ) := (scalar_family_hasDeriv hΦ p).deriv
  simp_rw [heq]
  exact (contDiff_infty_iff_fderiv.mp hΦ).2.clm_apply contDiff_const

lemma continuous_scalar_family_second {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    Continuous (fun p:ℝ×ℝ=>iteratedDeriv 2 (fun s=>Φ (p.1,s)) p.2) := by
  have H:=continuous_scalar_family_deriv (contDiff_scalar_family_deriv hΦ)
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using H

lemma scalar_family_contDiff {Φ : ℝ×ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (b:ℝ) :
    ContDiff ℝ ∞ (fun s=>Φ (b,s)) :=
  hΦ.comp (contDiff_const.prodMk contDiff_id)

end WeakMTWTransport

end

end OAI
