import OAI.Analysis.CircleDomains.Modulus.NormalizedArgumentBasic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

namespace OAI

/-! Smooth local logarithmic branches of the circular argument. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 def localArgumentBranch (a w : ℂ) : ℝ :=
  (Complex.log (w/a)).im / (2*Real.pi) + Complex.arg a / (2*Real.pi)

lemma localArgumentBranch_projects {a w : ℂ} (ha : a ≠ 0) (hw : w ≠ 0) :
    (localArgumentBranch a w : UnitAddCircle) = normalizedArgument w := by
  unfold localArgumentBranch
  rw [Complex.log_im, AddCircle.coe_add, ← normalizedArgument_eq,
    ← normalizedArgument_eq, ← normalizedArgument_mul (div_ne_zero hw ha) ha]
  rw [div_mul_cancel₀ _ ha]

lemma localArgumentBranch_smooth {a : ℂ} (ha : a ≠ 0) :
    ContDiffAt ℝ ∞ (localArgumentBranch a) a := by
  have hsl : a/a ∈ Complex.slitPlane := by simpa only [div_self ha] using Complex.one_mem_slitPlane
  have hv : ContDiffAt ℝ ∞ (fun w : ℂ => w/a) a := contDiffAt_id.div_const a
  have hh : ContDiffAt ℝ ∞ (fun w : ℂ => Complex.log (w/a)) a :=
    ((Complex.contDiffAt_log hsl).restrict_scalars ℝ).comp (f := fun w : ℂ => w/a) a hv
  exact ((Complex.imCLM.contDiff.contDiffAt.comp a hh).div_const _).add contDiffAt_const

end CircleDomainRigidity.FiniteTransfer

end

end OAI
