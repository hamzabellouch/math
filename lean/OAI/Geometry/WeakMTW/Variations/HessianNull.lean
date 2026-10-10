import Mathlib
import OAI.Geometry.WeakMTW.Variations.DiscreteVariationalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem bilinear_psd_null_sum (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v, 0 ≤ B v v) {v : E} (hv : B v v = 0) (w : E) :
    B v w + B w v = 0 := by
  by_contra hn
  let c := B v w + B w v
  have hc : c ≠ 0 := hn
  have hh := hB (w - ((B w w + 1)/c) • v)
  simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul,hv,mul_zero,sub_zero] at hh
  have he' : B w w - ((B w w+1)/c) * B w v - ((B w w+1)/c) * B v w = -1 := by
    field_simp [hc]
    dsimp [c]
    ring
  linarith

 theorem hessian_null_pair {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hm : IsLocalMin f x) {v : E} (hv : fderiv ℝ (fderiv ℝ f) x v v = 0) (w : E) :
    fderiv ℝ (fderiv ℝ f) x v w = 0 := by
  have hh := bilinear_psd_null_sum (fderiv ℝ (fderiv ℝ f) x) (hessian_nonneg hf hm) hv w
  have hs := (hf.isSymmSndFDerivAt (by norm_num)).eq v w
  linarith

end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
