import Mathlib
import OAI.Geometry.WeakMTW.Potentials.IntermediateDuality
import OAI.Geometry.WeakMTW.Potentials.ReverseGeodesic
import OAI.Geometry.WeakMTW.Potentials.IntermediateCoordinates
import OAI.Geometry.WeakMTW.Potentials.SmoothEnvelope

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

 theorem intermediate_coordinate_c11 (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (z : M) :
     ContDiffAt ℝ 1 (fun X : Model n => hopfLax t u ((chartAt (Model n) z).symm X))
       (chartAt (Model n) z z) ∧
     ∃ C : ℝ≥0, ∃ U ∈ 𝓝 (chartAt (Model n) z z),
       LipschitzOnWith C (fderiv ℝ (fun X : Model n => hopfLax t u ((chartAt (Model n) z).symm X))) U := by
   let e := potentialHomeomorph hMTW ⟨v,huv.2.1,huv.2.2.1⟩ ht ht1
   let q := e.symm z
   let x := q.val.1
   let y := exp q.val.1 q.val.2
   let c := chartAt (Model n) z
   let d := chartAt (Model n) x
   let b := chartAt (Model n) y
   let qX (X : Model n) := e.symm (c.symm X)
   let pole (X : Model n) := (qX X).val.1
   let endp (X : Model n) := exp (qX X).val.1 (qX X).val.2
   let P (X : Model n) := d (pole X)
   let Q (X : Model n) := b (endp X)
   have hz : z ∈ c.source := mem_chart_source (Model n) z
   have hZ : c z ∈ c.target := c.map_source hz
   have hq0 : qX (c z) = q := by simp only [qX,c.left_inv hz,q]
   have hp0 : pole (c z) = x := by simp only [pole,hq0,x]
   have he0 : endp (c z) = y :=
     congrArg (fun q : potentialGraph (n := n) u => exp q.val.1 q.val.2) hq0
   have hqx : ContinuousAt qX (c z) := e.symm.continuous.continuousAt.comp (c.symm.continuousAt hZ)
   have hpx : ContinuousAt pole (c z) :=
      (FiberBundle.continuous_proj (Model n) (TangentSpace (model n))).continuousAt.comp
       (continuous_subtype_val.continuousAt.comp hqx)
   have hex : ContinuousAt endp (c z) := exp_total_smooth.continuous.continuousAt.comp
     (continuous_subtype_val.continuousAt.comp hqx)
   have hd : ContinuousAt d (pole (c z)) := by rw [hp0]; exact d.continuousAt (mem_chart_source (Model n) x)
   have hb : ContinuousAt b (endp (c z)) := by rw [he0]; exact b.continuousAt (mem_chart_source (Model n) y)
   have hP : ContinuousAt P (c z) := hd.comp hpx
   have hQ : ContinuousAt Q (c z) := hb.comp hex
   have hgM := (cost_smooth_shortened ((globalSupportingProperty hMTW ⟨v,huv.2.1,huv.2.2.1⟩).1
     q.val.1 q.val.2 q.property).1 ht ht1)
   have hproj : exp q.val.1 (t•q.val.2) = z := e.apply_symm_apply z
   rw [hproj] at hgM
   let g : Model n×Model n → ℝ := fun A => cost (d.symm A.2) (c.symm A.1)/t
   let h : Model n×Model n → ℝ := fun A => -cost (c.symm A.1) (b.symm A.2)/(1-t)
   have hg : ContDiffAt ℝ ∞ g (c z,P (c z)) := by
     have hc := cost_coords_smooth (cost_smooth_swap hgM.1)
     have hc' := hc.div_const t
     have he : P (c z) = d x := congrArg d hp0
     rw [he]
     have hfun : g = (fun A : Model n×Model n => cost (c.symm A.1) (d.symm A.2)/t) := by
       funext A
       exact congrArg (fun r : ℝ => r/t) (cost_comm _ _)
     rw [hfun]
     exact hc'
   have hh : ContDiffAt ℝ ∞ h (c z,Q (c z)) := by
     have hc := (cost_coords_smooth hgM.2).neg.div_const (1-t)
     simpa only [h,Q,he0,b,c,y] using hc
   apply QuadraticEnvelope.two_sided_local hP hQ hg hh
   have hpS : ∀ᶠ X in 𝓝 (c z), pole X ∈ d.source := by
     apply hpx.preimage_mem_nhds
     rw [hp0]
     exact d.open_source.mem_nhds (mem_chart_source (Model n) x)
   have heS : ∀ᶠ X in 𝓝 (c z), endp X ∈ b.source := by
     apply hex.preimage_mem_nhds
     rw [he0]
     exact b.open_source.mem_nhds (mem_chart_source (Model n) y)
   filter_upwards [hpS,heS] with X hPX hQX Y
   have hs := intermediate_two_sided_supports hMTW huv ht ht1 (qX X)
   have hprojX : potentialProjection u t (qX X) = c.symm X := e.apply_symm_apply (c.symm X)
   rw [hprojX] at hs
   have hub := (hs.1 (c.symm Y)).2
   have hlb := (hs.1 (c.symm Y)).1
   change hopfLax t u (c.symm X)+(-cost (c.symm Y) (b.symm (b (endp X)))/(1-t))-
       (-cost (c.symm X) (b.symm (b (endp X)))/(1-t)) ≤ hopfLax t u (c.symm Y) ∧
     hopfLax t u (c.symm Y) ≤ hopfLax t u (c.symm X)+
       cost (d.symm (d (pole X))) (c.symm Y)/t-cost (d.symm (d (pole X))) (c.symm X)/t
   rw [b.left_inv hQX,d.left_inv hPX]
   constructor
   · dsimp only [endp]
     rw [neg_div,neg_div]
     linarith [hs.2.2]
   · dsimp only [pole]
     linarith [hs.2.1]

 theorem intermediate_c11 (hMTW : HasWeakMTW (n := n) (M := M))
     {u v : M → ℝ} (huv : IsDualPair u v) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
     ManifoldC11 (n := n) (hopfLax t u) := by
   refine ⟨fun z => ?_,fun z => (intermediate_coordinate_c11 hMTW huv ht ht1 z).2⟩
   let c := chartAt (Model n) z
   have hz : z ∈ c.source := mem_chart_source (Model n) z
   have hf := contMDiffAt_iff_contDiffAt.mpr (intermediate_coordinate_c11 hMTW huv ht ht1 z).1
   have hc : ContMDiffAt (model n) 𝓘(ℝ,Model n) 1 c z :=
     contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hz)
   have hh := hf.comp z hc
   apply hh.congr_of_eventuallyEq
   filter_upwards [c.open_source.mem_nhds hz] with z' hz'
   change hopfLax t u z' = hopfLax t u (c.symm (c z'))
   rw [c.left_inv hz']
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
