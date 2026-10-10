import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateUniformBounds
import OAI.Geometry.WeakMTW.Potentials.PositiveEnvelope

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold NNReal
namespace WeakMTW
noncomputable section
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]
open QuadraticEnvelope RiemannianLocal ChartMetric

 def growthGap (a : ℝ×TangentBundle (model n) M) (x : M) : ℝ :=
   cost x (intermediateCenter a)/a.1 - cost x (intermediateCenter ((1+a.1)/2,a.2))/((1+a.1)/2)

 theorem growthGap_local_min {a : ℝ×TangentBundle (model n) M}
     (ht : 0 < a.1) (ht1 : a.1 < 1) (ha : a.2 ∈ totalMinimizingSet) :
     IsMinOn (growthGap a) univ a.2.1 := by
   let s := (1+a.1)/2
   have hts : a.1 < s := by dsimp [s]; linarith
   have hs1 : s < 1 := by dsimp [s]; linarith
   have hc := radialSplitAction_contact a.2.1 ha ht hts hs1
   intro x _
                                                                                          
   have hin := cost_triangle_split x (intermediateCenter a)
     (intermediateCenter (s,a.2)) ht (sub_pos.mpr hts)
   dsimp [growthGap,intermediateCenter]
                                                         
   have hcontact : cost a.2.1 (exp a.2.1 (a.1•a.2.2))/a.1 +
       cost (exp a.2.1 (a.1•a.2.2)) (exp a.2.1 (s•a.2.2))/(s-a.1) -
       cost a.2.1 (exp a.2.1 (s•a.2.2))/s = 0 := by
     simpa only [radialSplitAction,Prod.fst,Prod.snd,add_zero,
       (chartAt (Model n) a.2.1).left_inv (mem_chart_source (Model n) a.2.1)] using hc
   dsimp only [intermediateCenter] at hin
   have he : a.1+(s-a.1)=s := by ring
   rw [he] at hin
   change _ ≤ cost x (exp a.2.1 (a.1•a.2.2))/a.1 - cost x (exp a.2.1 (s•a.2.2))/s
   change cost a.2.1 (exp a.2.1 (a.1•a.2.2))/a.1 - cost a.2.1 (exp a.2.1 (s•a.2.2))/s ≤ _
   linarith

 theorem growthGap_positive {a : ℝ×TangentBundle (model n) M}
     (ht : 0 < a.1) (ht1 : a.1 < 1) (ha : a.2 ∈ totalMinimizingSet)
     {w : Model n} (hw : w ≠ 0) :
     0 < fderiv ℝ (fderiv ℝ (fun X => growthGap a ((chartAt (Model n) a.2.1).symm X)))
       ((chartAt (Model n) a.2.1) a.2.1) w w := by
   let s := (1+a.1)/2
   have hts : a.1 < s := by dsimp [s]; linarith
   have hs1 : s < 1 := by dsimp [s]; linarith
   let L := tangentCoordinateEquiv a.2.1 a.2.1 (mem_chart_source (Model n) a.2.1)
   let ξ := L.symm w
   have hξ : ξ ≠ 0 := by
     intro h
     apply hw
     rw [←L.apply_symm_apply w]
     change L ξ = 0
     rw [h,map_zero]
   have hL : tangentChartLinear a.2.1 ξ = w := by
     rw [←tangentCoordinateEquiv_center]
     exact L.apply_symm_apply w
   have hpos := radial_hessian_strict a.2.1 ha ht hts hs1 hξ
   have he := radialSplitAction_hessian a.2.1 ha ht hts hs1 ξ
   rw [hL] at he
   have hf := (initialCost_geometry a.2.1 (strict_radial_mem_injectivity ha ht.le ht1)).1.of_le
     (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
   have hg := (initialCost_geometry a.2.1 (strict_radial_mem_injectivity ha (ht.trans hts).le hs1)).1.of_le
     (show (2:ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
   have h₁ := DiscreteVariational.hessian_split hf hg a.1 s
     (cost (exp a.2.1 (a.1•a.2.2)) (exp a.2.1 (s•a.2.2))/(s-a.1)) w
   have h₂ := DiscreteVariational.hessian_split hf hg a.1 s 0 w
   have heq : (fun X => radialSplitAction a.2.1 a.2.2 a.1 s (X,0)) =
       (fun X => initialCost a.2.1 (exp a.2.1 (a.1•a.2.2)) X/a.1 +
       cost (exp a.2.1 (a.1•a.2.2)) (exp a.2.1 (s•a.2.2))/(s-a.1) -
       initialCost a.2.1 (exp a.2.1 (s•a.2.2)) X/s) := by
      funext X; simp only [radialSplitAction,add_zero,initialCost]
   rw [heq,h₁] at he
   simp only [add_zero,initialCost] at h₂
   change 0 < fderiv ℝ (fderiv ℝ (fun X => cost ((chartAt (Model n) a.2.1).symm X)
     (exp a.2.1 (a.1•a.2.2))/a.1 - cost ((chartAt (Model n) a.2.1).symm X)
     (exp a.2.1 (s•a.2.2))/s)) _ w w
   rw [h₂,he]
   linarith

 theorem growthGap_local_positive_bounds {a : ℝ×TangentBundle (model n) M}
     (ht : 0 < a.1) (ht1 : a.1 < 1) (ha : a.2 ∈ totalMinimizingSet) :
     ∃ U : Set (ℝ×TangentBundle (model n) M), IsOpen U ∧ a ∈ U ∧ ∃ r κ : ℝ,
       0 < r ∧ 0 < κ ∧ ∀ a' ∈ U, ∀ X ∈ Metric.ball (chartAt (Model n) a.2.1 a.2.1) r,
       ContDiffAt ℝ 2 (fun Y => growthGap a' ((chartAt (Model n) a.2.1).symm Y)) X ∧
       ∀ w : Model n, κ*‖w‖^2 ≤ fderiv ℝ (fderiv ℝ
         (fun Y => growthGap a' ((chartAt (Model n) a.2.1).symm Y))) X w w := by
   let S (a' : ℝ×TangentBundle (model n) M) := ((1+a'.1)/2,a'.2)
   have hS : Continuous S := ((continuous_const.add continuous_fst).div_const 2).prodMk continuous_snd
   let c := chartAt (Model n) a.2.1
   let d := chartAt (Model n) (intermediateCenter a)
   let e := chartAt (Model n) (intermediateCenter (S a))
   let P (a' : ℝ×TangentBundle (model n) M) :=
     (a'.1,(d (intermediateCenter a'),e (intermediateCenter (S a'))))
   let g : Model n×(ℝ×(Model n×Model n)) → ℝ := fun W =>
     cost (c.symm W.1) (d.symm W.2.2.1)/W.2.1 -
       cost (c.symm W.1) (e.symm W.2.2.2)/((1+W.2.1)/2)
   have hP : ContinuousAt P a := continuousAt_fst.prodMk
     (((d.continuousAt (mem_chart_source (Model n) (intermediateCenter a))).comp
       intermediateCenter_continuous.continuousAt).prodMk
     (ContinuousAt.comp (f := fun a' => intermediateCenter (S a')) (g := e)
       (e.continuousAt (mem_chart_source (Model n) (intermediateCenter (S a))))
       (intermediateCenter_continuous.comp hS).continuousAt))
   have hs0 : 0 < (1+a.1)/2 := by linarith
   have hs1 : (1+a.1)/2 < 1 := by linarith
   have hc := cost_coords_smooth (cost_smooth_at_injectivity a.2.1
     (strict_radial_mem_injectivity ha ht.le ht1))
   have hd := cost_coords_smooth (cost_smooth_at_injectivity a.2.1
     (strict_radial_mem_injectivity ha hs0.le hs1))
   have hg₁ : ContDiffAt ℝ ∞ (fun W : Model n×(ℝ×(Model n×Model n)) =>
       cost (c.symm W.1) (d.symm W.2.2.1)) (c a.2.1,P a) :=
     hc.comp (c a.2.1,P a) (contDiffAt_fst.prodMk contDiffAt_snd.snd.fst)
   have hg₂ : ContDiffAt ℝ ∞ (fun W : Model n×(ℝ×(Model n×Model n)) =>
       cost (c.symm W.1) (e.symm W.2.2.2)) (c a.2.1,P a) :=
     hd.comp (c a.2.1,P a) (contDiffAt_fst.prodMk contDiffAt_snd.snd.snd)
   have hg : ContDiffAt ℝ ∞ g (c a.2.1,P a) :=
     (hg₁.div contDiffAt_snd.fst ht.ne').sub
       (hg₂.div ((contDiffAt_const.add contDiffAt_snd.fst).div_const 2) hs0.ne')
   apply family_positive_bounds hP hg _ (fun w hw => growthGap_positive ht ht1 ha hw)
   have hnear₁ : ∀ᶠ a' in 𝓝 a, intermediateCenter a' ∈ d.source :=
     intermediateCenter_continuous.continuousAt.preimage_mem_nhds
       (d.open_source.mem_nhds (mem_chart_source (Model n) (intermediateCenter a)))
   have hnear₂ : ∀ᶠ a' in 𝓝 a, intermediateCenter (S a') ∈ e.source :=
     (intermediateCenter_continuous.comp hS).continuousAt.preimage_mem_nhds
       (e.open_source.mem_nhds (mem_chart_source (Model n) (intermediateCenter (S a))))
   filter_upwards [hnear₁,hnear₂] with a' h₁ h₂ X
   dsimp only [g,P]
   rw [d.left_inv h₁,e.left_inv h₂]
   rfl
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
