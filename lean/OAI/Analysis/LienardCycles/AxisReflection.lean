import OAI.Analysis.LienardCycles.AxisIntercept

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScaledProfile ScalarArcs
lemma poly_neg (a : Fin 6 → ℝ) (x : ℝ) : poly (-a) x= -poly a x := by
  dsimp [poly]
  ring
lemma endpoint_neg (a : Fin 6 → ℝ) {h t : ℝ} (hh : 0<h) (ht : h<t) :
    endpoint (-a) false h t= -endpoint a true h t ∧ endpoint (-a) true h t= -endpoint a false h t := by
  have ha := chosen_arch (positive_arch_exists (φ_smooth a) hh ht)
  have hb := ArchSymmetries.IsArch.reflect ha
  have he : (fun x=>-φ a x)=φ (-a) := by funext x; exact (poly_neg a _).symm
  rw [he] at hb
  exact canonical_of_positive_arch hb (φ_smooth (-a)) hh ht
lemma axisEndpoint_neg (a : Fin 6 → ℝ) {t : ℝ} (ht : 0<t) :
    axisEndpoint (-a) false t= -axisEndpoint a true t ∧ axisEndpoint (-a) true t= -axisEndpoint a false t := by
  have he : ∀ᶠ h in 𝓝[>] (0:ℝ), endpoint (-a) false h t= -endpoint a true h t ∧
      endpoint (-a) true h t= -endpoint a false h t := by
    filter_upwards [self_mem_nhdsWithin,(eventually_lt_nhds ht).filter_mono inf_le_left] with h hh hht
    exact endpoint_neg a hh hht
  constructor
  · exact tendsto_nhds_unique (lower_axis_tendsto (φ_smooth (-a)) (φ_continuous (-a)).continuousOn ht)
      (((upper_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).neg).congr' (he.mono fun _ h=>h.1.symm))
  · exact tendsto_nhds_unique (upper_axis_tendsto (φ_smooth (-a)) (φ_continuous (-a)).continuousOn ht)
      (((lower_axis_tendsto (φ_smooth a) (φ_continuous a).continuousOn ht).neg).congr' (he.mono fun _ h=>h.2.symm))
lemma transversePeaks_neg (a : Fin 6 → ℝ) : transversePeaks (-a)=transversePeaks a := by
  ext t
  change (0<t ∧ _ ∧ _) ↔ (0<t ∧ _ ∧ _)
  constructor <;> intro ht
  · rw [(axisEndpoint_neg a ht.1).1,(axisEndpoint_neg a ht.1).2,poly_neg] at ht
    exact ⟨ht.1,by linarith [ht.2.2],by linarith [ht.2.1]⟩
  · refine ⟨ht.1,?_,?_⟩ <;> simp only [(axisEndpoint_neg a ht.1).1,(axisEndpoint_neg a ht.1).2,poly_neg] <;> linarith [ht.2.1,ht.2.2]
lemma axisWidth_neg (a : Fin 6 → ℝ) {t : ℝ} (ht : 0<t) : axisWidth (-a) t=axisWidth a t := by
  dsimp only [axisWidth]
  rw [(axisEndpoint_neg a ht).1,(axisEndpoint_neg a ht).2]
  ring
lemma axisWidths_neg (a : Fin 6 → ℝ) : axisWidths (-a)=axisWidths a := by
  unfold axisWidths
  rw [transversePeaks_neg]
  apply image_congr
  intro t ht
  exact axisWidth_neg a ht.1
lemma axisFit_neg (a : Fin 6 → ℝ) {r : ℝ} (hr : r ∈ axisWidths a) :
    axisLambda (-a) r= -axisLambda a r ∧ axisKappa (-a) r= -axisKappa a r := by
  have hr' : r ∈ axisWidths (-a) := by rwa [axisWidths_neg]
  have ha := joint_limits a hr (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _=>r)
    self_mem_nhdsWithin (tendsto_id.mono_left inf_le_left) tendsto_const_nhds
  have hb := joint_limits (-a) hr' (l:=𝓝[>] (0:ℝ)) (h:=id) (r:=fun _=>r)
    self_mem_nhdsWithin (tendsto_id.mono_left inf_le_left) tendsto_const_nhds
  have he : ∀ᶠ h in 𝓝[>] (0:ℝ), QuinticFit.lambda (-a) (h,r)= -QuinticFit.lambda a (h,r) ∧
      QuinticFit.kappa (-a) (h,r)= -QuinticFit.kappa a (h,r) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact QuinticFit.fit_neg a hh (axisM_abs_lt a hr).1
  constructor
  · exact tendsto_nhds_unique hb.2.2.1 (ha.2.2.1.neg.congr' (he.mono fun _ h=>h.1.symm))
  · exact tendsto_nhds_unique hb.2.2.2.1 (ha.2.2.2.1.neg.congr' (he.mono fun _ h=>h.2.symm))
lemma axisLambda_gt {a : Fin 6 → ℝ} {r d : ℝ} (hr : r ∈ axisWidths a)
    (hp : ∀ u,0<u → u*curvature a u-slope a u+d<0)
    (hs : Tendsto (slope a) (𝓝[>] 0) atTop) : d<axisLambda a r := by
  have hr' : r ∈ axisWidths (-a) := by rwa [axisWidths_neg]
  have hp' : ∀ u,0<u → 0<u*curvature (-a) u-slope (-a) u+(-d) := by
    intro u hu
    rw [curvature_neg,slope_neg]
    linarith [hp u hu]
  have hs' : Tendsto (slope (-a)) (𝓝[>] 0) atBot := by
    change Tendsto (fun x=>slope (-a) x) _ _
    simpa only [slope_neg,Function.comp_def] using tendsto_neg_atTop_atBot.comp hs
  have hl := axisLambda_lt hr' hp' hs'
  rw [(axisFit_neg a hr).1] at hl
  linarith
end QuinticLienard.AxisFlow

end OAI
