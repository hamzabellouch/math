import Mathlib
import OAI.Geometry.Cannon.Beltrami.Mollifier
import OAI.Geometry.Cannon.Conformal.WeakQSInverseShrink

namespace OAI

section
section
section
section
section
section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap Real Topology ContDiff

noncomputable section
open MeasureTheory Filter FourierTransform Set Metric
open scoped Real SchwartzMap ContDiff Topology

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section
open Set Topology

noncomputable section
open Set Metric Filter Topology

noncomputable section
open Set Filter Topology Metric

noncomputable section
open Set Filter Topology
open MeasureTheory
open scoped ENNReal

noncomputable section
open Set Metric Filter Topology

noncomputable section
open MeasureTheory Filter Set Metric Function ContinuousLinearMap
open scoped Topology Convolution ContDiff Pointwise

noncomputable section
namespace CannonBeltrami
open CannonPlane

theorem global_metric_weak_mrmt (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume)
    {k : ℝ} (hk : 0 ≤ k) (hk1 : k < 1) (hb : ∀ z, ‖μ z‖ ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℂ ≃ₜ ℂ, H 0=0 ∧ H 1=1 ∧
      CannonMetricQC.WeakQS H C ∧ CannonMetricQC.WeakQS H.symm C ∧
      ∀ S : Set ℂ, IsCompact S → ∃ a : Lp ℂ 2 (volume.restrict S),
        ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
          (∫ z, H z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
          (∫ z, H z*partialBar φ z)=-(∫ z in S, a z*(μ z*φ z)) := by
  obtain ⟨ν,hνc,hνb,hνlim⟩ := global_smooth_coefficient_approximation hm hk hb
  choose F hF0 hF1 hF hF' hFe hFD hFD' using
    (fun n => normalized_smooth_beltrami_solution (ν n) (hνc n) hk hk1 (hνb n))
  let K := (1+k)/(1-k)
  have hK : 0 ≤ K := div_nonneg (by linarith) (sub_pos.mpr hk1).le
  obtain ⟨H,σ,hσ,hH0,hH1,hlim,hlim'⟩ := normalized_smooth_qc_subsequence F hF0 hF1
    (fun n => (hF n).of_le (by simp)) (fun n => (hF' n).of_le (by simp)) hK hFD hFD'
  have hr : UniformRelativeControl (fun n z => F n z) := by
    intro ε hε
    obtain ⟨η,hη,h⟩ := smooth_qc_uniform_shrink hK ε hε
    exact ⟨η,hη,fun n => h (F n) ((hF' n).of_le (by simp)) (hFD' n)⟩
  have hp := normalized_family_pointwise_bound (fun n z => F n z) hF0 hF1 hr
  have he := relative_control_equicontinuous (fun n z => F n z) hr hp
  have hlocal (S : Set ℂ) (hS : IsCompact S) :
      ∃ B : ℝ, 0 ≤ B ∧ ∀ n z, z ∈ S → ‖F (σ n) z‖ ≤ B := by
    obtain ⟨B,hB,hbB⟩ := equicontinuous_compact_bound (fun n z => F n z) he hp hS
    exact ⟨B,hB,fun n => hbB (σ n)⟩
  have hpt (z : ℂ) : Tendsto (fun n => F (σ n) z) atTop (𝓝 (H z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H) |>.comp hlim
  have hνt : ∀ᵐ z ∂volume, Tendsto (fun n => ν (σ n) z) atTop (𝓝 (μ z)) := by
    filter_upwards [hνlim] with z hz
    exact hz.comp hσ.tendsto_atTop
  have hpt' (z : ℂ) : Tendsto (fun n => (F (σ n)).symm z) atTop (𝓝 (H.symm z)) :=
    (continuous_eval_const z).tendsto (homeomorphMap H.symm) |>.comp hlim'
  obtain ⟨η,hη,hs⟩ := smooth_qc_uniform_shrink hK (1/2) (by norm_num)
  have hsh : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (H a) (H x) ≤ (1/2:ℝ)*dist (H b) (H x) := by
    intro x a b hb hab
    apply le_of_tendsto_of_tendsto ((hpt a).dist (hpt x))
      (((hpt b).dist (hpt x)).const_mul (1/2))
    exact Eventually.of_forall (fun n => (hs (F (σ n))
      ((hF' (σ n)).of_le (by simp)) (hFD' (σ n)) x a b hb hab).le)
  have hshi : ∀ x a b : ℂ, b ≠ x → dist a x < η*dist b x →
      dist (H.symm a) (H.symm x) ≤ (1/2:ℝ)*dist (H.symm b) (H.symm x) := by
    intro x a b hb hab
    apply le_of_tendsto_of_tendsto ((hpt' a).dist (hpt' x))
      (((hpt' b).dist (hpt' x)).const_mul (1/2))
    exact Eventually.of_forall (fun n => (hs (F (σ n)).symm
      ((hF (σ n)).of_le (by simp)) (hFD (σ n)) x a b hb hab).le)
  refine ⟨η⁻¹,inv_pos.mpr hη,H,hH0,hH1,
    CannonMetricQC.weakQS_of_inverse_shrink H hη hshi,
    CannonMetricQC.weakQS_of_inverse_shrink H.symm hη hsh,fun S hS => ?_⟩
  exact local_weak_beltrami_limit (fun n => F (σ n)) H (fun n => hF (σ n)) hlocal hpt hK
    (fun n => hFD (σ n)) (fun n => ν (σ n)) μ
    (fun n => (ν (σ n)).continuous.aestronglyMeasurable) hm hk (fun n => hνb (σ n)) hb hνt
    (fun n => hFe (σ n)) hS

end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
