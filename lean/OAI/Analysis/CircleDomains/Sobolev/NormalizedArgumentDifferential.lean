import OAI.Analysis.CircleDomains.Sobolev.LocalArgumentBranch
import OAI.Analysis.CircleDomains.Modulus.NormalizedArgument
import OAI.Analysis.CircleDomains.Sobolev.CircleDifferential
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! Smooth local logarithmic branches and the exact differential of
argument in turns on the punctured plane. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

lemma localArgumentBranch_fderiv {a : ℂ} (ha : a ≠ 0) (v : ℂ) :
    fderiv ℝ (localArgumentBranch a) a v = (v/a).im / (2*Real.pi) := by
  have hsl : a/a ∈ Complex.slitPlane := by simpa only [div_self ha] using Complex.one_mem_slitPlane
  have hd : HasDerivAt (fun w : ℂ => Complex.log (w/a)) a⁻¹ a := by
    simpa only [id_eq, div_self ha, div_one, one_div] using ((hasDerivAt_id a).div_const a).clog hsl
  have hi := Complex.imCLM.hasFDerivAt.comp a (hd.hasFDerivAt.restrictScalars ℝ)
  have hh := (hi.mul_const (2*Real.pi)⁻¹).add_const (Complex.arg a/(2*Real.pi))
  have he : localArgumentBranch a =
      (fun w => (Complex.imCLM (Complex.log (w/a))) * (2*Real.pi)⁻¹ +
        Complex.arg a/(2*Real.pi)) := by
    funext w
    simp only [localArgumentBranch, Complex.imCLM_apply, div_eq_mul_inv]
  dsimp only [Function.comp_def] at hh
  rw [he, hh.fderiv]
  change (2*Real.pi)⁻¹ * (v * a⁻¹).im = _
  simp only [div_eq_mul_inv]
  ring

lemma smoothCircleOn_normalizedArgument :
    SmoothCircleOn normalizedArgument {z : ℂ | z ≠ 0} := by
  apply smoothCircleOn_iff_local_lifts.mpr
  intro a ha
  refine ⟨localArgumentBranch a, localArgumentBranch_smooth ha, ?_⟩
  filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds ha] with w hw
  exact localArgumentBranch_projects ha hw

lemma circleFDeriv_normalizedArgument {a : ℂ} (ha : a ≠ 0) (v : ℂ) :
    circleFDeriv normalizedArgument a v = (v/a).im/(2*Real.pi) := by
  have he : (fun w => (localArgumentBranch a w : UnitAddCircle)) =ᶠ[𝓝 a] normalizedArgument := by
    filter_upwards [isOpen_ne_fun continuous_id continuous_const |>.mem_nhds ha] with w hw
    exact localArgumentBranch_projects ha hw
  rw [circleFDeriv_eq_lift (continuousAt_normalizedArgument ha)
    (localArgumentBranch_smooth ha).continuousAt he]
  exact localArgumentBranch_fderiv ha v

end CircleDomainRigidity.FiniteTransfer

end

end OAI
