import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactQuadratic
import OAI.Analysis.BiholderTransport.CostGeometry.CrossingUniform

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section UniformMiddle
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma uniform_suffix_crossing_bounds :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ s∈Icc (1/4:ℝ) (3/4), ∀ v,
      c*‖v‖^2≤ radialCrossingValue (sprayFlow (1/4) z).1
        (s • (sprayFlow (1/4) z).2) v/s^2 ∧
      radialCrossingValue (sprayFlow (1/4) z).1
        (s • (sprayFlow (1/4) z).2) v/s^2≤ C*‖v‖^2 := by
  let G := {z : TangentBundle 𝓘(ℝ,Model n) M | z.2∈minimizingVectors z.1}
  let F : ℝ × TangentBundle 𝓘(ℝ,Model n) M → TangentBundle 𝓘(ℝ,Model n) M :=
    fun q => tangentScale q.1 (sprayFlow (1/4) q.2)
  have hF : Continuous F := contMDiff_tangentScale.continuous.comp
    (continuous_fst.prodMk (contMDiff_sprayFlow.continuous.comp
      (continuous_const.prodMk continuous_snd)))
  have hK : IsCompact (F '' (Icc (1/4:ℝ) (3/4) ×ˢ G)) :=
    (isCompact_Icc.prod (isCompact_total_minimizingVectors (n := n) (M := M))).image hF
  have hI : ∀ z∈F '' (Icc (1/4:ℝ) (3/4) ×ˢ G), z.2∈injectivityDomain z.1 := by
    rintro _ ⟨⟨s,z⟩,hsz,rfl⟩
    have H := proper_suffix_in_injectivityDomain hsz.2 (show (0:ℝ)<1/4 by norm_num)
      (show (1/4:ℝ)<s+1/4 by linarith [hsz.1.1])
      (show s+1/4≤(1:ℝ) by linarith [hsz.1.2])
    change s • (sprayFlow (1/4) z).2∈injectivityDomain (sprayFlow (1/4) z).1
    simpa only [add_sub_cancel_right] using H
  obtain ⟨c,C,hc,hC,H⟩ := compact_bundle_radialCrossingValue_bounds hK hI
  refine ⟨c,16*C,hc,mul_pos (by norm_num) hC,?_⟩
  intro z hz s hs v
  have hb := H (F (s,z)) (mem_image_of_mem _ ⟨hs,hz⟩) v
  change c*‖v‖^2≤ radialCrossingValue (sprayFlow (1/4) z).1
      (s • (sprayFlow (1/4) z).2) v ∧
    radialCrossingValue (sprayFlow (1/4) z).1
      (s • (sprayFlow (1/4) z).2) v≤ C*‖v‖^2 at hb
  have hp : 0<s := by linarith [hs.1]
  have hslo : (1/16:ℝ)≤ s^2 := by nlinarith [hs.1]
  have hshi : s^2≤(1:ℝ) := by nlinarith [hs.2]
  constructor
  · rw [le_div_iff₀ (sq_pos_of_pos hp)]
    exact (mul_le_of_le_one_right (mul_nonneg hc.le (sq_nonneg ‖v‖)) hshi).trans hb.1
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    have hmul := mul_le_mul_of_nonneg_left hslo (mul_nonneg hC.le (sq_nonneg ‖v‖))
    nlinarith [hb.2]

lemma uniform_middleHessian_crossing :
    ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2∈minimizingVectors z.1 → ∀ δ : ℝ, 0≤δ → δ≤1/2 → ∀ v,
      c*δ*‖v‖^2≤ middleHessian z (1/4) (1-δ) v v-middleHessian z (1/4) 1 v v ∧
      middleHessian z (1/4) (1-δ) v v-middleHessian z (1/4) 1 v v≤ C*δ*‖v‖^2 := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_suffix_crossing_bounds (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd hdhalf v
  let p := (sprayFlow (1/4) z).2
  let x := (sprayFlow (1/4) z).1
  let Q : ℝ → ℝ := fun r => radialCrossingValue x (r • p) v/r^2
  let f : ℝ → ℝ := fun r => normalHessian x (r • p) v v/r
  have hI (r) (hr : r∈Icc (1/4:ℝ) (3/4)) : r • p∈injectivityDomain x := by
    have HH := proper_suffix_in_injectivityDomain hz (show (0:ℝ)<1/4 by norm_num)
      (show (1/4:ℝ)<r+1/4 by linarith [hr.1])
      (show r+1/4≤(1:ℝ) by linarith [hr.2])
    simpa only [add_sub_cancel_right] using HH
  have hder (r) (hr : r∈Icc (1/4:ℝ) (3/4)) : HasDerivAt f (-Q r) r :=
    divided_normalHessian_derivative_value (by linarith [hr.1]) (hI r hr) v
  have hf : ContinuousOn f (Icc (1/4:ℝ) (3/4)) :=
    fun r hr => (hder r hr).continuousAt.continuousWithinAt
  have hdf : DifferentiableOn ℝ f (interior (Icc (1/4:ℝ) (3/4))) :=
    fun r hr => (hder r (interior_subset hr)).differentiableAt.differentiableWithinAt
  have hs : 1-δ-1/4∈Icc (1/4:ℝ) (3/4) := ⟨by linarith,by linarith⟩
  have ht : (3/4:ℝ)∈Icc (1/4:ℝ) (3/4) := ⟨by norm_num,le_rfl⟩
  have hst : 1-δ-1/4≤(3/4:ℝ) := by linarith
  have hlo := (convex_Icc (1/4:ℝ) (3/4)).image_sub_le_mul_sub_of_deriv_le hf hdf
    (C := -(c*‖v‖^2)) (fun r hr => by
      rw [(hder r (interior_subset hr)).deriv]
      exact neg_le_neg (H z hz r (interior_subset hr) v).1)
    (1-δ-1/4) hs (3/4) ht hst
  have hhi := (convex_Icc (1/4:ℝ) (3/4)).mul_sub_le_image_sub_of_le_deriv hf hdf
    (C := -(C*‖v‖^2)) (fun r hr => by
      rw [(hder r (interior_subset hr)).deriv]
      exact neg_le_neg (H z hz r (interior_subset hr) v).2)
    (1-δ-1/4) hs (3/4) ht hst
  rw [middleHessian_apply,middleHessian_apply]
  change _≤_ + f (1-δ-1/4)-(_+f (1-1/4)) ∧
    _+f (1-δ-1/4)-(_+f (1-1/4))≤_
  norm_num only [show (1:ℝ)-1/4=3/4 by norm_num]
  constructor <;> nlinarith

end UniformMiddle
end WeakMTWTransport

end

end

end

end OAI
