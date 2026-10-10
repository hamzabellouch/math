import Mathlib
import OAI.Geometry.WeakMTW.Variations.DiscreteVariationalCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter
open scoped Topology ContDiff
namespace DiscreteVariational
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem derivative_hessian_along_curve {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F : V → ℝ} {c : ℝ → V} {k : V}
    (hF : ContDiffAt ℝ 2 F (c 0)) (hc : HasDerivAt c k 0) (w : V) :
    HasDerivAt (fun t => fderiv ℝ F (c t) w)
      (fderiv ℝ (fderiv ℝ F) (c 0) k w) 0 := by
  have hd := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hp := hd.hasFDerivAt.comp_hasDerivAt 0 hc
  have hh := hp.clm_apply (hasDerivAt_const (0 : ℝ) w)
  convert! hh using 1
  simp

 theorem generating_focal_hessian {F : (E × E) × E → ℝ} {Y : E × E → E}
    {G : E → E →L[ℝ] E →L[ℝ] ℝ} {q : E × E} {κ : E}
    (hF : ContDiffAt ℝ 2 F (q,Y q)) (hY : DifferentiableAt ℝ Y q)
    (hker : fderiv ℝ Y q (0,κ) = 0)
    (hgrad : ∀ᶠ r in 𝓝 q, ∀ a b : E,
      fderiv ℝ F (r,Y r) ((a,b),0) = -G r.1 r.2 a) (a b : E) :
    fderiv ℝ (fderiv ℝ F) (q,Y q) ((0,κ),0) ((a,b),0) = -G q.1 κ a := by
  let r : ℝ → E × E := fun t => q+t•(0,κ)
  have hr₀ : r 0 = q := by simp [r]
  have hr : HasDerivAt r (0,κ) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const ((0,κ) : E × E)).const_add q using 1
    first | rfl | simp
  have hy : HasDerivAt (Y ∘ r) 0 0 := by
    have hd : HasFDerivAt Y (fderiv ℝ Y q) (r 0) := by simpa only [hr₀] using hY.hasFDerivAt
    simpa only [hker] using hd.comp_hasDerivAt 0 hr
  have hp : HasDerivAt (fun t => (r t,Y (r t))) ((0,κ),0) 0 := hr.prodMk hy
  have hF' : ContDiffAt ℝ 2 F (r 0,Y (r 0)) := by simpa only [hr₀] using hF
  have hh := derivative_hessian_along_curve hF' hp (((a,b),0) : (E × E) × E)
  have he : (fun t => fderiv ℝ F (r t,Y (r t)) ((a,b),0)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => -G q.1 (q.2+t•κ) a) := by
    have htend : Tendsto r (𝓝 (0 : ℝ)) (𝓝 q) := by simpa only [hr₀] using hr.continuousAt.tendsto
    filter_upwards [htend hgrad] with t ht
    have hfst : (r t).1 = q.1 := by change q.1+t•(0 : E) = q.1; simp
    have hsnd : (r t).2 = q.2+t•κ := rfl
    change ∀ a b : E, fderiv ℝ F (r t,Y (r t)) ((a,b),0) = -G (r t).1 (r t).2 a at ht
    rw [hfst,hsnd] at ht
    exact ht a b
  have hlin : HasDerivAt (fun t : ℝ => -G q.1 (q.2+t•κ) a) (-G q.1 κ a) 0 := by
    have hk := ((hasDerivAt_id (0 : ℝ)).smul_const κ).const_add q.2
    convert! ((G q.1).hasFDerivAt.comp_hasDerivAt 0 hk |>.clm_apply (hasDerivAt_const (0 : ℝ) a)).neg using 1
    simp
  simpa only [hr₀] using hh.unique (hlin.congr_of_eventuallyEq he)

 theorem vertical_min_hessian_nonneg {F : (E × E) × E → ℝ} {q : E × E} {z : E}
    (hF : ContDiffAt ℝ 2 F (q,z))
    (hm : IsLocalMin (fun v : E => F ((q.1,v),z)) q.2) (κ : E) :
    0 ≤ fderiv ℝ (fderiv ℝ F) (q,z) ((0,κ),0) ((0,κ),0) := by
  let L : E →L[ℝ] (E × E) × E :=
    ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)).prod (0 : E →L[ℝ] E)
  let A : E → (E × E) × E := fun v => ((q.1,v),z)
  have hA : ContDiff ℝ ∞ A := (contDiff_const.prodMk contDiff_id).prodMk contDiff_const
  have hDA : ∀ v, HasFDerivAt A L v := fun v =>
    ((hasFDerivAt_const (c := q.1) v).prodMk (hasFDerivAt_id v)).prodMk (hasFDerivAt_const (c := z) v)
  have hcomp : ContDiffAt ℝ 2 (F ∘ A) q.2 := hF.comp q.2 (hA.contDiffAt.of_le (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  have hc : fderiv ℝ (fderiv ℝ (F ∘ A)) q.2 κ κ =
      fderiv ℝ (fderiv ℝ F) (q,z) (L κ) (L κ) := by
    have hdf := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hFnear : ∀ᶠ u in 𝓝 (q,z), DifferentiableAt ℝ F u :=
      (hF.eventually (by norm_num)).mono (fun _ h => h.differentiableAt (by norm_num))
    have he : fderiv ℝ (F ∘ A) =ᶠ[𝓝 q.2] (fun v => (fderiv ℝ F (A v)).comp L) := by
      filter_upwards [hA.continuous.continuousAt.preimage_mem_nhds hFnear] with v hv
      exact (hv.hasFDerivAt.comp v (hDA v)).fderiv
    have hd := (hdf.hasFDerivAt.comp q.2 (hDA q.2)).clm_comp (hasFDerivAt_const (c := L) q.2)
    rw [(hd.congr_of_eventuallyEq he).fderiv]
    simp
  have hh := hessian_nonneg hcomp hm κ
  rw [hc] at hh
  exact hh

end
end DiscreteVariational
end

end WeakMTWGlobalSupport

end OAI
