import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeRegularization
import OAI.Geometry.TamingCompatibility.Hodge.HodgeSmoothSpatial
import OAI.Geometry.TamingCompatibility.HeatFlow.HodgePairingHeat

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume HodgeFrame Set
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (g : ContMDiffRiemannianMetric Model ∞ Space (TangentSpace Model : X → Type))

def unitFrameDirection (u : MetricUnit g) : FrameSpace A := fun i =>
  eval (globalFrame J α ht A E i.1 i.2) u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)

attribute [local irreducible] frameDecode unitFrameDirection

def unitDual (u : MetricUnit g) : PreL2 A J α hs ht true :=
  ⟨fun z => frameDecode J α ht A E z (unitFrameDirection A J α ht E g u),by
    have hv : ContMDiff Model 𝓘(ℝ,FrameSpace A) ∞
        (fun _ : X => unitFrameDirection A J α ht E g u) := contMDiff_const
    exact frameDecode_section_smooth J α ht A E hE hs _ hv⟩

include hE in
omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
lemma framePairing_direction (a : TwoForm X) (u : MetricUnit g) :
    framePairing A J α ht E a u.val.proj (unitFrameDirection A J α ht E g u) =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  have he := globalFrame_full_resolution J α ht A E hE a u.val.proj
  have hh := congrArg (fun b : MetricForms.Form Space 2 =>
    b ![u.val.2,J.endomorphism u.val.proj u.val.2]) he
  let v : A.centers → Fin 6 → MetricForms.Form Space 2 := fun p j =>
    globalFrame J α ht A E p j u.val.proj
  let c : A.centers → Fin 6 → ℝ := fun p j => (squareMass A u.val.proj)⁻¹ *
    GeometricAdjoint.pairing J α ht a (globalFrame J α ht A E p j) u.val.proj
  change (∑ p : A.centers, ∑ j : Fin 6, c p j • v p j)
    ![u.val.2,J.endomorphism u.val.proj u.val.2] =
    a u.val.proj ![u.val.2,J.endomorphism u.val.proj u.val.2] at hh
  simp only [ContinuousAlternatingMap.sum_apply,ContinuousAlternatingMap.smul_apply,smul_eq_mul] at hh
  calc
    _ = ∑ p : A.centers, ∑ j : Fin 6,
        ((squareMass A u.val.proj)⁻¹ * GeometricAdjoint.pairing J α ht a
          (globalFrame J α ht A E p j) u.val.proj) *
          eval (globalFrame J α ht A E p j) u.val.proj u.val.2
            (J.endomorphism u.val.proj u.val.2) := by
      simp only [framePairing,_root_.sum_apply,_root_.smul_apply,
        ContinuousLinearMap.proj_apply,smul_eq_mul,Finset.mul_sum,unitFrameDirection,mul_assoc]
    _ = _ := hh

omit [MeasurableSpace X] [BorelSpace X] in
lemma unitDual_pairing (a : TwoForm X) (u : MetricUnit g) :
    GeometricAdjoint.pairing J α ht (unitDual A J α hs ht E hE g u).val a u.val.proj =
      eval a u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2) := by
  rw [← framePairing_direction A J α ht E hE g a u,framePairing_apply]
  exact MetricForms.pairing_symm _ _ _

variable {A J α hs ht E hE g}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source}
  {r : ℝ} {hr : 0 < r} (C : HodgeSmoothingCover A J α hs ht D hD r hr)

lemma pairingEvaluation_unitDual (u : MetricUnit g) :
    C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj = C.evaluation g u := by
  have he : (fun f => C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj f) =
      (fun f => C.evaluation g u f) :=
    (hodgeSmoothShift_cube_dense A J α hs ht D hD r hr).equalizer
      (C.pairingEvaluation (unitDual A J α hs ht E hE g u) u.val.proj).continuous
      (C.evaluation g u).continuous (by
        funext a
        dsimp only [Function.comp_apply]
        rw [C.pairingEvaluation_smooth _ _ _ a
          (hodgeRegularization_smoothShift_cube A J α hs ht r hr a),
          C.evaluation_smooth g u _ a (hodgeRegularization_smoothShift_cube A J α hs ht r hr a)]
        exact unitDual_pairing A J α hs ht E hE g a.val u)
  ext f
  exact congrFun he f

lemma pairingEvaluationVector_unitDual (u : MetricUnit g) :
    C.pairingEvaluationVector (unitDual A J α hs ht E hE g u) u.val.proj = C.evaluationVector g u := by
  unfold HodgeSmoothingCover.pairingEvaluationVector HodgeSmoothingCover.evaluationVector
  rw [pairingEvaluation_unitDual C u]

lemma pairingHeatVector_unitDual (u : MetricUnit g) :
    C.pairingHeatVector (unitDual A J α hs ht E hE g u) u.val.proj = C.heatEvaluationVector g u := by
  unfold HodgeSmoothingCover.pairingHeatVector HodgeSmoothingCover.heatEvaluationVector
    HodgeSmoothingCover.pairingHeatEvaluation HodgeSmoothingCover.heatEvaluation
  rw [pairingEvaluation_unitDual C u]

lemma pairingGammaTail_unitDual (T : ℝ) (hT : 0 ≤ T) (s : ℝ) (u v : MetricUnit g) :
    C.pairingGammaTail T hT s (unitDual A J α hs ht E hE g v)
      (unitDual A J α hs ht E hE g u) u.val.proj v.val.proj = C.gammaTailKernel g T hT s u v := by
  unfold HodgeSmoothingCover.pairingGammaTail HodgeSmoothingCover.gammaTailKernel
  rw [pairingHeatVector_unitDual C u,pairingHeatVector_unitDual C v]

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end

end OAI
