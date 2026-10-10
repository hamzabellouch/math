import OAI.Geometry.NodalSets.Elliptic.SeedLogarithmicBranch

namespace OAI

namespace Yau.Target
open Filter
open scoped ContDiff Topology
noncomputable section

lemma seedLog_direction_hasFDerivAt {x : SeedAmbient} (hx : x ∈ seedLogDomain)
    (v : SeedAmbient) :
    HasFDerivAt (fun y ↦ fderiv ℝ seedLog y v)
      ((seedQuadratic x)⁻¹ • (seedZ2 v • seedZ1 + seedZ1 v • seedZ2) -
        (seedQuadraticDerivative x v / seedQuadratic x ^ 2) • seedQuadraticDerivative x) x := by
  have he : (fun y ↦ fderiv ℝ seedLog y v) =ᶠ[𝓝 x]
      (fun y ↦ seedQuadraticDerivative y v / seedQuadratic y) := by
    filter_upwards [seedLogDomain_open.mem_nhds hx] with y hy
    exact seedLog_fderiv hy v
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) (Complex.slitPlane_ne_zero hx)).comp x
    (seedQuadratic_hasFDerivAt x)
  have hd := (seedQuadraticDerivative_apply_hasFDerivAt x v).mul hi
  have he' : (fun y ↦ fderiv ℝ seedLog y v) =ᶠ[𝓝 x]
      (fun y ↦ seedQuadraticDerivative y v * (seedQuadratic y)⁻¹) := by
    simpa only [div_eq_mul_inv] using he
  convert! hd.congr_of_eventuallyEq he' using 1
  ext w
  simp [ContinuousLinearMap.mulLeftRight_apply,div_eq_mul_inv,pow_two]
  ring

lemma seedLog_second {x : SeedAmbient} (hx : x ∈ seedLogDomain) (v w : SeedAmbient) :
    fderiv ℝ (fderiv ℝ seedLog) x w v =
      (seedZ2 v * seedZ1 w + seedZ1 v * seedZ2 w) / seedQuadratic x -
      seedQuadraticDerivative x v * seedQuadraticDerivative x w / seedQuadratic x ^ 2 := by
  have hs := (seedLog_contDiffAt hx).fderiv_right (m := ∞) (by simp)
  have he := (hs.differentiableAt (by simp)).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hh := congrArg (fun L : SeedAmbient →L[ℝ] ℂ ↦ L w)
    (he.fderiv.symm.trans (seedLog_direction_hasFDerivAt hx v).fderiv)
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,mul_add] using hh

lemma seedLogReal_second {x : SeedAmbient} (hx : x ∈ seedLogDomain) (v w : SeedAmbient) :
    fderiv ℝ (fderiv ℝ seedLogReal) x w v =
      ((seedZ2 v * seedZ1 w + seedZ1 v * seedZ2 w) / seedQuadratic x -
      seedQuadraticDerivative x v * seedQuadraticDerivative x w / seedQuadratic x ^ 2).re := by
  have he : (fun y ↦ fderiv ℝ seedLogReal y v) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ seedLog y v).re) := by
    filter_upwards [seedLogDomain_open.mem_nhds hx] with y hy
    rw [(seedLogReal_hasFDerivAt hy).fderiv,(seedLog_hasFDerivAt hy).fderiv]
    rfl
  have hs : ContDiffAt ℝ ∞ seedLogReal x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (seedLog_contDiffAt hx)
  have hd := ((hs.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v x)
  have hr := Complex.reCLM.hasFDerivAt.comp x (seedLog_direction_hasFDerivAt hx v)
  have hh := congrArg (fun L : SeedAmbient →L[ℝ] ℝ ↦ L w)
    (hd.fderiv.symm.trans (he.fderiv_eq.trans hr.fderiv))
  simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,mul_add] using hh

end
end Yau.Target

end OAI
