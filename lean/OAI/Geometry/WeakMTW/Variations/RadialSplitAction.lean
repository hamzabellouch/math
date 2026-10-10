import Mathlib
import OAI.Geometry.WeakMTW.Variations.ActionHessian
import OAI.Geometry.WeakMTW.Variations.CostSplitting
import OAI.Geometry.WeakMTW.Variations.RadialComparisonCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def radialSplitAction (x : M) (a : TangentSpace (model n) x) (s t : ℝ)
    (q : Model n × TangentSpace (model n) x) : ℝ :=
    cost ((chartAt (Model n) x).symm q.1) (exp x (s•a+q.2)) / s +
    cost (exp x (s•a+q.2)) (exp x (t•a)) / (t-s) -
    cost ((chartAt (Model n) x).symm q.1) (exp x (t•a)) / t

 omit [IsManifold (model n) ∞ M]
   [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
   [IsRiemannianManifold (model n) M] [CompactSpace M] in
 theorem radialSplitAction_nonneg (x : M) (a : TangentSpace (model n) x)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (q : Model n × TangentSpace (model n) x) :
    0 ≤ radialSplitAction x a s t q := by
  have hh := cost_triangle_split ((chartAt (Model n) x).symm q.1)
    (exp x (s•a+q.2)) (exp x (t•a)) hs (sub_pos.mpr hst)
  rw [add_sub_cancel] at hh
  exact sub_nonneg.mpr hh

 theorem radialSplitAction_contact (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    radialSplitAction x a s t (chartAt (Model n) x x,0) = 0 := by
  unfold radialSplitAction
  simp only [add_zero,(chartAt (Model n) x).left_inv (mem_chart_source (Model n) x)]
  rw [minimizing_shortened_cost ha hs.le (hst.trans ht).le,
    minimizing_shortened_cost ha (hs.trans hst).le ht.le]
  have htail := minimizing_shortened_dist ha hs.le hst.le ht.le
  change s^2*‖a‖^2/2/s+(dist (exp x (s•a)) (exp x (t•a)))^2/2/(t-s)-t^2*‖a‖^2/2/t=0
  rw [htail]
  field_simp [hs.ne', (hs.trans hst).ne', (sub_pos.mpr hst).ne']
  ring

 theorem radialSplitAction_min (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    IsLocalMin (radialSplitAction x a s t) (chartAt (Model n) x x,0) := by
  filter_upwards [] with q
  rw [radialSplitAction_contact x ha hs hst ht]
  exact radialSplitAction_nonneg x a hs hst q

 theorem radialSplitAction_smooth (x : M) {a : TangentSpace (model n) x}
    (ha : a ∈ minimizingDomain x) {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ContDiffAt ℝ ∞ (radialSplitAction x a s t) (chartAt (Model n) x x,0) := by
  let c := chartAt (Model n) x
  let q₀ : Model n × TangentSpace (model n) x := (c x,0)
  have hxC : ContMDiffAt 𝓘(ℝ,Model n) (model n) ∞ c.symm (c x) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds (c.map_source (mem_chart_source (Model n) x)))
  have hX : ContMDiffAt 𝓘(ℝ,Model n × TangentSpace (model n) x) (model n) ∞
      (fun q => c.symm q.1) q₀ := hxC.comp q₀ (contMDiffAt_iff_contDiffAt.mpr contDiffAt_fst)
  have hY : ContMDiff 𝓘(ℝ,Model n × TangentSpace (model n) x) (model n) ∞
      (fun q : Model n × TangentSpace (model n) x => exp x (s•a+q.2)) :=
    (exp_fibre_smooth x).comp (contMDiff_iff_contDiff.mpr (contDiff_const.add contDiff_snd))
  have hZ : ContMDiffAt 𝓘(ℝ,Model n × TangentSpace (model n) x) (model n) ∞
      (fun _ => exp x (t•a)) q₀ := contMDiffAt_const
  have hsI := strict_radial_mem_injectivity ha hs.le (hst.trans ht)
  have htI := strict_radial_mem_injectivity ha (hs.trans hst).le ht
  have hcost₁ := cost_smooth_at_injectivity x hsI
  have hcost₃ := cost_smooth_at_injectivity x htI
  let p : TangentBundle (model n) M := ⟨x,a⟩
  let q := geodesicFlow s p
  have htail := minimizing_tail_injectivity ha hs.le hst ht
  have hcost₂ := cost_smooth_at_injectivity q.1 htail.1
  rw [htail.2] at hcost₂
  have hqbase : q.1 = exp x (s•a) := (exp_mul_eq_geodesic p s).symm
  rw [hqbase] at hcost₂
  have h₁ : ContMDiffAt 𝓘(ℝ,Model n × TangentSpace (model n) x) 𝓘(ℝ,ℝ) ∞
      (fun q => cost (c.symm q.1) (exp x (s•a+q.2))) q₀ := by
    have hcc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
        (fun z : M × M => cost z.1 z.2) (c.symm q₀.1,exp x (s•a+q₀.2)) := by
      simpa only [q₀,Prod.fst,Prod.snd,add_zero,c.left_inv (mem_chart_source (Model n) x)] using hcost₁
    exact hcc.comp q₀ (hX.prodMk hY.contMDiffAt)
  have h₂ : ContMDiffAt 𝓘(ℝ,Model n × TangentSpace (model n) x) 𝓘(ℝ,ℝ) ∞
      (fun q => cost (exp x (s•a+q.2)) (exp x (t•a))) q₀ := by
    have hcc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
        (fun z : M × M => cost z.1 z.2) (exp x (s•a+q₀.2),exp x (t•a)) := by
      simpa only [q₀,Prod.snd,add_zero] using hcost₂
    exact hcc.comp q₀ (hY.contMDiffAt.prodMk hZ)
  have h₃ : ContMDiffAt 𝓘(ℝ,Model n × TangentSpace (model n) x) 𝓘(ℝ,ℝ) ∞
      (fun q => cost (c.symm q.1) (exp x (t•a))) q₀ := by
    have hcc : ContMDiffAt ((model n).prod (model n)) 𝓘(ℝ,ℝ) ∞
        (fun z : M × M => cost z.1 z.2) (c.symm q₀.1,exp x (t•a)) := by
      simpa only [q₀,Prod.fst,c.left_inv (mem_chart_source (Model n) x)] using hcost₃
    exact hcc.comp q₀ (hX.prodMk hZ)
  exact ((contMDiffAt_iff_contDiffAt.mp h₁).div_const s |>.add
    ((contMDiffAt_iff_contDiffAt.mp h₂).div_const (t-s))).sub
      ((contMDiffAt_iff_contDiffAt.mp h₃).div_const t)

 theorem radialSplitAction_initial_derivative (x : M) (a u : TangentSpace (model n) x)
    (s t : ℝ) (hu : s•a+u ∈ injectivityDomain x) (ht : t•a ∈ injectivityDomain x)
    (hf : DifferentiableAt ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,u))
    (w : Model n) :
    fderiv ℝ (radialSplitAction x a s t) (chartAt (Model n) x x,u) (w,0) =
      -(metric x (chartAt (Model n) x x) (tangentChartLinear x (s•a+u)) w) / s +
      (metric x (chartAt (Model n) x x) (tangentChartLinear x (t•a)) w) / t := by
  rw [← DiscreteVariational.fderiv_partial_fst hf]
  have hf₁ := ((initialCost_geometry x hu).1.differentiableAt (by simp)).hasFDerivAt
  have hf₃ := ((initialCost_geometry x ht).1.differentiableAt (by simp)).hasFDerivAt
  have hd := ((hf₁.mul_const s⁻¹).add_const (cost (exp x (s•a+u)) (exp x (t•a)) / (t-s))).sub (hf₃.mul_const t⁻¹)
  change fderiv ℝ (fun z => initialCost x (exp x (s•a+u)) z / s +
    cost (exp x (s•a+u)) (exp x (t•a)) / (t-s) - initialCost x (exp x (t•a)) z / t)
      (chartAt (Model n) x x) w = _
  simp only [div_eq_mul_inv]
  have hde : fderiv ℝ (fun z => initialCost x (exp x (s•a+u)) z * s⁻¹ +
      cost (exp x (s•a+u)) (exp x (t•a)) / (t-s) -
      initialCost x (exp x (t•a)) z * t⁻¹) (chartAt (Model n) x x) =
      s⁻¹ • fderiv ℝ (initialCost x (exp x (s•a+u))) (chartAt (Model n) x x) -
      t⁻¹ • fderiv ℝ (initialCost x (exp x (t•a))) (chartAt (Model n) x x) := hd.fderiv
  simp only [div_eq_mul_inv] at hde
  rw [hde]
  simp only [sub_apply,smul_apply,smul_eq_mul]
  rw [(initialCost_geometry x hu).2.1,(initialCost_geometry x ht).2.1]
  ring

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
