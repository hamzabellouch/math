import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeUnitDual

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

include hs hE in
lemma unitFrameDirection_continuous : Continuous (unitFrameDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (globalFrame J α ht A E i.1 i.2)
    (globalFrame_smooth J α ht A E hE hs i.1 i.2)).continuous

def unitFrameFunctional (u : MetricUnit g) : FrameSpace A →L[ℝ] ℝ :=
  (squareMass A u.val.proj)⁻¹ • ∑ p : A.centers, ∑ j : Fin 6,
    unitFrameDirection A J α ht E g u (p,j) •
      (ContinuousLinearMap.proj (p,j) : FrameSpace A →L[ℝ] ℝ)

lemma unitFrameFunctional_eq (u : MetricUnit g) :
    unitFrameFunctional A J α ht E g u =
      framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj := by
  unfold unitFrameFunctional framePairing
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro j _
  rw [unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E p j) u]
  rfl

lemma unitDual_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj ((unitDual A J α hs ht E hE g u).val u.val.proj) =
      unitFrameDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  exact unitDual_pairing A J α hs ht E hE g (globalFrame J α ht A E i.1 i.2) u

include hs hE in
lemma unitFrameFunctional_continuous : Continuous (unitFrameFunctional A J α ht E g) := by
  have hb : Continuous (fun u : MetricUnit g => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  unfold unitFrameFunctional
  apply ((squareMass_inv_smooth A).continuous.comp hb).smul
  apply continuous_finsetSum
  intro p _
  apply continuous_finsetSum
  intro j _
  exact ((continuous_apply (p,j)).comp
    (unitFrameDirection_continuous A J α hs ht E hE g)).smul continuous_const

include hs hE in
lemma unitFrame_uniform : ∃ B : ℝ, 0 ≤ B ∧ ∀ u : MetricUnit g,
    ‖unitFrameDirection A J α ht E g u‖ ≤ B ∧ ‖unitFrameFunctional A J α ht E g u‖ ≤ B := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameDirection_continuous A J α hs ht E hE g).continuousOn
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitFrameFunctional_continuous A J α hs ht E hE g).continuousOn
  refine ⟨max 0 (max B C),le_max_left _ _,fun u => ⟨?_,?_⟩⟩
  · exact (hB u (mem_univ _)).trans ((le_max_left B C).trans (le_max_right _ _))
  · exact (hC u (mem_univ _)).trans ((le_max_right B C).trans (le_max_right _ _))

lemma currentFrame_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ u v : MetricUnit g,
    ∀ K : FrameSpace A →L[ℝ] FrameSpace A,
    |framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
      (K (frameEncode J α ht A E v.val.proj ((unitDual A J α hs ht E hE g v).val v.val.proj)))| ≤
        B * ‖K‖ := by
  obtain ⟨B,hB,hbound⟩ := unitFrame_uniform A J α hs ht E hE g
  refine ⟨B^2,sq_nonneg _,fun u v K => ?_⟩
  rw [unitDual_encode,← unitFrameFunctional_eq A J α hs ht E hE g]
  calc
    _ ≤ ‖unitFrameFunctional A J α ht E g u‖ * ‖K (unitFrameDirection A J α ht E g v)‖ :=
      (unitFrameFunctional A J α ht E g u).le_opNorm _
    _ ≤ B * (‖K‖ * B) := mul_le_mul (hbound u).2
      ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbound v).1 (norm_nonneg _)))
      (norm_nonneg _) hB
    _ = B^2*‖K‖ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def unitStarDirection (u : MetricUnit g) : FrameSpace A := fun i =>
  eval (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u.val.proj u.val.2
    (J.endomorphism u.val.proj u.val.2)

include hs hE in
omit [MeasurableSpace X] [BorelSpace X] in
lemma unitStarDirection_continuous : Continuous (unitStarDirection A J α ht E g) := by
  apply continuous_pi
  intro i
  exact (unitEvaluation J g (starTwo J α ht (globalFrame J α ht A E i.1 i.2))
    (starTwo_smooth J α hs ht (globalFrame_smooth J α ht A E hE hs i.1 i.2))).continuous

lemma unitDual_star_encode (u : MetricUnit g) :
    frameEncode J α ht A E u.val.proj
      ((preStar A J α hs ht (unitDual A J α hs ht E hE g u)).val u.val.proj) =
      unitStarDirection A J α ht E g u := by
  ext i
  rw [frameEncode_apply]
  change GeometricAdjoint.pairing J α ht
    (starTwo J α ht (unitDual A J α hs ht E hE g u).val)
    (globalFrame J α ht A E i.1 i.2) u.val.proj = _
  rw [hodgeStar_pairing]
  exact unitDual_pairing A J α hs ht E hE g
    (starTwo J α ht (globalFrame J α ht A E i.1 i.2)) u

lemma wedgeFrame_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ u v : MetricUnit g,
    ∀ K : FrameSpace A →L[ℝ] FrameSpace A,
    |framePairing A J α ht E (unitDual A J α hs ht E hE g u).val u.val.proj
      (K (frameEncode J α ht A E v.val.proj
        ((preStar A J α hs ht (unitDual A J α hs ht E hE g v)).val v.val.proj)))| ≤
        B * ‖K‖ := by
  obtain ⟨B,hB,hbound⟩ := unitFrame_uniform A J α hs ht E hE g
  obtain ⟨L,hL⟩ := isCompact_univ.exists_bound_of_continuousOn
    (unitStarDirection_continuous A J α hs ht E hE g).continuousOn
  let M := max 0 L
  have hM : 0 ≤ M := le_max_left _ _
  have hm (v : MetricUnit g) : ‖unitStarDirection A J α ht E g v‖ ≤ M :=
    (hL v (mem_univ _)).trans (le_max_right _ _)
  refine ⟨B*M,mul_nonneg hB hM,fun u v K => ?_⟩
  rw [unitDual_star_encode,← unitFrameFunctional_eq A J α hs ht E hE g]
  calc
    _ ≤ ‖unitFrameFunctional A J α ht E g u‖ * ‖K (unitStarDirection A J α ht E g v)‖ :=
      (unitFrameFunctional A J α ht E g u).le_opNorm _
    _ ≤ B * (‖K‖ * M) := mul_le_mul (hbound u).2
      ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hm v) (norm_nonneg _)))
      (norm_nonneg _) hB
    _ = B*M*‖K‖ := by ring

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
