import Mathlib
import OAI.Geometry.WeakMTW.Potentials.ChartLocalLipschitz
import OAI.Geometry.WeakMTW.Potentials.IntermediateGrowthLocal

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

 theorem growthGap_local_metric {a : ℝ×TangentBundle (model n) M}
     (ht : 0 < a.1) (ht1 : a.1 < 1) (ha : a.2 ∈ totalMinimizingSet) :
     ∃ U : Set (ℝ×TangentBundle (model n) M), IsOpen U ∧ a ∈ U ∧ ∃ r κ : ℝ,
       0 < r ∧ 0 < κ ∧ ∀ a' ∈ U, 0 < a'.1 → a'.1 < 1 → a'.2 ∈ totalMinimizingSet →
       ∀ x : M, dist a'.2.1 x < r → κ*(dist a'.2.1 x)^2 ≤ growthGap a' x-growthGap a' a'.2.1 := by
   obtain ⟨U,hU,haU,R,K,hR,hK,hbound⟩ := growthGap_local_positive_bounds ht ht1 ha
   obtain ⟨S,B,hS,hB,hT,hlip⟩ := chart_inverse_local_lipschitz (E := Model n) a.2.1
   let c := chartAt (Model n) a.2.1
   have hsrc : a.2.1 ∈ c.source := mem_chart_source (Model n) a.2.1
   have hnear : c.source ∩ c ⁻¹' Metric.ball (c a.2.1) (min R S) ∈ 𝓝 a.2.1 :=
     inter_mem (c.open_source.mem_nhds hsrc)
       ((c.continuousAt hsrc).preimage_mem_nhds (Metric.ball_mem_nhds _ (lt_min hR hS)))
   obtain ⟨ε,hε,hεb⟩ := Metric.mem_nhds_iff.mp hnear
   have hp : Continuous (fun a' : ℝ×TangentBundle (model n) M => a'.2.1) :=
     (contMDiff_proj (TangentSpace (model n)) (IB := model n) (n := ∞)).continuous.comp continuous_snd
   let V := U ∩ (fun a' : ℝ×TangentBundle (model n) M => a'.2.1) ⁻¹' Metric.ball a.2.1 (ε/3)
   refine ⟨V,hU.inter (Metric.isOpen_ball.preimage hp),⟨haU,by simp [hε]⟩,
     ε/3,K/(2*(B:ℝ)^2),by positivity,by positivity,?_⟩
   intro a' ha' ht' ht1' hmin' x hx
   have hax : a'.2.1 ∈ Metric.ball a.2.1 ε := Metric.ball_subset_ball (by linarith) ha'.2
   have hxx : x ∈ Metric.ball a.2.1 ε := by
     rw [Metric.mem_ball,dist_comm x a.2.1]
     have hmm : dist a.2.1 a'.2.1 < ε/3 := by simpa only [mem_preimage,Metric.mem_ball,dist_comm] using ha'.2
     exact (dist_triangle a.2.1 a'.2.1 x).trans_lt (by linarith)
   have hA := hεb hax
   have hX := hεb hxx
   have hAR : c a'.2.1 ∈ Metric.ball (c a.2.1) R := Metric.ball_subset_ball (min_le_left _ _) hA.2
   have hXR : c x ∈ Metric.ball (c a.2.1) R := Metric.ball_subset_ball (min_le_left _ _) hX.2
   have hAS : c a'.2.1 ∈ Metric.ball (c a.2.1) S := Metric.ball_subset_ball (min_le_right _ _) hA.2
   have hXS : c x ∈ Metric.ball (c a.2.1) S := Metric.ball_subset_ball (min_le_right _ _) hX.2
   have hd := hlip.dist_le_mul (x := c x) hXS (y := c a'.2.1) hAS
   rw [c.left_inv hX.1,c.left_inv hA.1,dist_comm x a'.2.1,dist_eq_norm] at hd
   have hlocal : IsLocalMin (fun Y => growthGap a' (c.symm Y)) (c a'.2.1) := by
     apply Eventually.of_forall
     intro Y
     change growthGap a' (c.symm (c a'.2.1)) ≤ growthGap a' (c.symm Y)
     rw [c.left_inv hA.1]
     exact growthGap_local_min ht' ht1' hmin' (mem_univ _)
   have hf := (hbound a' ha'.1 (c a'.2.1) hAR).1.differentiableAt (by norm_num)
   have hz := hlocal.hasFDerivAt_eq_zero hf.hasFDerivAt
   have hgap := positive_hessian_growth (hbound a' ha'.1) hAR hXR hz
   rw [c.left_inv hA.1,c.left_inv hX.1] at hgap
   have hsq : (dist a'.2.1 x)^2 ≤ (B:ℝ)^2*‖c x-c a'.2.1‖^2 := by
     simpa only [mul_pow] using pow_le_pow_left₀ dist_nonneg hd 2
   have hgrow : K/(2*(B:ℝ)^2)*(dist a'.2.1 x)^2 ≤ K/2*‖c x-c a'.2.1‖^2 := by
     have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ K/(2*(B:ℝ)^2) by positivity)
     have heq : K/(2*(B:ℝ)^2)*((B:ℝ)^2*‖c x-c a'.2.1‖^2) =
         K/2*‖c x-c a'.2.1‖^2 := by
       field_simp
     rwa [heq] at hh
   exact hgrow.trans hgap
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI
