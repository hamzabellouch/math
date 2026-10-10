import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgePairingIntegral

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization Set MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
attribute [local instance] unitMeasurable unitBorel unitT2
namespace HodgeSmoothingCover
variable {ρ : ℝ} {hρ : 0 < ρ} (C : HodgeSmoothingCover A J α hs ht D hD ρ hρ)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def gammaWedgeTailKernel (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) : ℝ :=
  ⟪C.heatEvaluationVector g u,
    hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)
      (l2Star A J α hs ht (C.heatEvaluationVector g v))⟫

lemma gammaWedgeTailKernel_continuous (T : ℝ) (hT : 0 ≤ T) (r : ℝ) :
    Continuous (fun p : MetricUnit g × MetricUnit g => C.gammaWedgeTailKernel g T hT r p.1 p.2) :=
  ((C.heatEvaluationVector_continuous g).comp continuous_fst).inner
    ((hodgeGammaShift A J α hs ht D hD T hT r (2*ρ^2)).continuous.comp
      ((l2Star A J α hs ht).continuous.comp ((C.heatEvaluationVector_continuous g).comp continuous_snd)))

lemma gammaWedgeTailKernel_bound (T : ℝ) (hT : 0 ≤ T) (r : ℝ) (u v : MetricUnit g) :
    |C.gammaWedgeTailKernel g T hT r u v| ≤
      (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*
        ‖C.heatEvaluationVector g u‖*‖C.heatEvaluationVector g v‖ := by
  apply (abs_real_inner_le_norm _ _).trans
  have hh := mul_le_mul_of_nonneg_left
    (hodgeGammaShiftLinear_bound A J α hs ht D hD T hT r (2*ρ^2)
      (l2Star A J α hs ht (C.heatEvaluationVector g v)))
    (norm_nonneg (C.heatEvaluationVector g u))
  rw [l2Star_norm] at hh
  exact hh.trans_eq (by ring)

lemma gammaWedgeTailKernel_uniform (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, ∀ u v : MetricUnit g,
      |C.gammaWedgeTailKernel g T hT r u v| ≤ (1/120 : ℝ)*HodgeKernelBounds.gammaTail (T/r^2)*B^2 := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (C.heatEvaluationVector_continuous g).continuousOn
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hb (u : MetricUnit g) : ‖C.heatEvaluationVector g u‖ ≤ M :=
    (hB u (mem_univ _)).trans (le_max_left _ _)
  refine ⟨M,hM,fun r u v => (C.gammaWedgeTailKernel_bound g T hT r u v).trans ?_⟩
  have htail : 0 ≤ HodgeKernelBounds.gammaTail (T/r^2) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hsp
    exact mul_nonneg (Real.exp_pos _).le (pow_nonneg ((div_nonneg hT (sq_nonneg r)).trans_lt hsp).le _)
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul (hb u) (hb v) (norm_nonneg _) hM)
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 1/120) htail)
  simpa only [sq,mul_assoc] using hh

end HodgeSmoothingCover
end TamingCompatibility.GeometricHilbert

end
end

end

end OAI
