import Mathlib
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgeHeatEvaluation
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingIntegral

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

lemma hodgeGammaTailAction_factor_pair {T r ρ : ℝ} (hT : 0 ≤ T) (hr : 0 < r)
    (hρ : 2*ρ^2 ≤ T) (f g : L2 A J α hs ht true) :
    ⟪f,hodgeGammaTailAction A J α hs ht D hD T r g⟫ =
      ⟪hodgeSpectralHeat A J α hs ht D hD (ρ^2) f,
        hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
          (hodgeSpectralHeat A J α hs ht D hD (ρ^2) g)⟫ := by
  rw [hodgeGammaTailAction_factor A J α hs ht D hD hT hr hρ,
    hodgeSpectralHeat_symmetric]

variable [T2Space X]
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {A J α hs ht D hD} {ρ : ℝ} {hρ : 0 < ρ}
  (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

lemma gammaTailKernel_rapid {T : ℝ} (hT : 0 < T) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r → ∀ u v : MetricUnit g,
      |C.gammaTailKernel g T hT.le r u v| ≤ B*r^(2*N) := by
  obtain ⟨M,hM,hb⟩ := C.gammaTailKernel_uniform g T hT.le
  let B := ((1/120 : ℝ)*HodgeKernelBounds.moment 5 (1/2)*(N.factorial : ℝ)*(2/T)^N)*M^2
  have hB : 0 ≤ B := by
    have hm := (HodgeKernelBounds.moment_pos 5 (by norm_num : (0:ℝ)<1/2)).le
    dsimp [B]
    positivity
  refine ⟨B,hB,fun r hr u v => (hb r u v).trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (HodgeKernelBounds.gammaTail_small_scale N hT hr)
      (by norm_num : (0:ℝ)≤1/120)) (sq_nonneg M)
  exact hh.trans_eq (by dsimp [B]; ring)

lemma gammaTailKernel_pair (T : ℝ) (hT : 0 ≤ T) (r : ℝ)
    (μ ν : Measure (MetricUnit g)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ⟪C.heatRegularize g μ,
      hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2) (C.heatRegularize g ν)⟫ =
      ∫ u, ∫ v, C.gammaTailKernel g T hT r u v ∂ν ∂μ := by
  let K := hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
  have hμ := C.heatEvaluationVector_integrable g μ
  have hν := C.heatEvaluationVector_integrable g ν
  rw [heatRegularize,heatRegularize,← K.integral_comp_comm hν]
  have hi : Integrable (fun v => K (C.heatEvaluationVector g v)) ν := K.integrable_comp hν
  have hp := (innerSL ℝ (∫ v, K (C.heatEvaluationVector g v) ∂ν)).integral_comp_comm hμ
  simp only [innerSL_apply_apply] at hp
  rw [real_inner_comm,← hp]
  apply integral_congr_ae
  filter_upwards [] with u
  have h := (innerSL ℝ (C.heatEvaluationVector g u)).integral_comp_comm hi
  simpa only [innerSL_apply_apply,gammaTailKernel,real_inner_comm] using h.symm

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
