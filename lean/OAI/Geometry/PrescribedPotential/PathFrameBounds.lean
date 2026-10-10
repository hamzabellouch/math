import Mathlib
import OAI.Geometry.PrescribedPotential.CoordinateBalls
import OAI.Geometry.PrescribedPotential.FrameCompactBounds
import OAI.Geometry.PrescribedPotential.MatrixJetDirection
import OAI.Geometry.PrescribedPotential.PathRicci

namespace OAI

/-! Path Frame Bounds. -/

section

 

noncomputable section
open Set Metric Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
namespace CoordinateBall
variable (p : CoordinateBall A)

lemma path_frame_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x ∈ p.source,
      ∀ B : Matrix (Fin d) (Fin d) ℂ,
      -C*(frameGram (g.matrix p.index (A.chart p.index x)) B)^2 ≤
        frameResidual (pathLogDetHessian g h p.index t (A.chart p.index x))
          (g.matrix p.index (A.chart p.index x))
          (curvatureDiagonal (g.matrix p.index) (A.chart p.index x)) B := by
  let K : Set (ℝ × EC d) := Icc 0 1 ×ˢ closedBall p.center p.radius
  have hk (q : ℝ × EC d) (hq : q ∈ K) : coordinateEquiv d q.2 ∈ (A.chart p.index).target := by
    have he := p.closure_sub (closedBall_subset_closedBall (by linarith [p.radius_pos]) hq.2)
    simpa only [ComplexAtlas.euclideanChart_target,mem_preimage] using he
  have hmap : Continuous (fun q : ℝ × EC d => (q.1,coordinateEquiv d q.2)) :=
    continuous_fst.prodMk ((coordinateEquiv d).continuous.comp continuous_snd)
  have ha : ContinuousOn (fun q : ℝ × EC d => pathLogDetHessian g h p.index q.1 (coordinateEquiv d q.2)) K :=
    (pathLogDetHessian_continuous g h p.index).comp (f := fun q : ℝ × EC d => (q.1,coordinateEquiv d q.2)) hmap.continuousOn (fun q hq => ⟨mem_univ _,hk q hq⟩)
  have hg : ContinuousOn (fun q : ℝ × EC d => g.matrix p.index (coordinateEquiv d q.2)) K :=
    (g.smooth p.index).continuousOn.comp (f := fun q : ℝ × EC d => coordinateEquiv d q.2)
      ((coordinateEquiv d).continuous.comp continuous_snd).continuousOn hk
  have hr := curvatureDiagonal_joint_continuous (A.chart p.index).open_target (g.smooth p.index)
    (fun z hz => ne_of_gt (g.positive p.index z hz).det_pos)
  have hR : ContinuousOn (fun q : (ℝ × EC d) × V d =>
      curvatureDiagonal (g.matrix p.index) (coordinateEquiv d q.1.2) q.2) (K ×ˢ univ) := by
    apply hr.comp (f := fun q : (ℝ × EC d) × V d => (coordinateEquiv d q.1.2,q.2))
    · exact (((coordinateEquiv d).continuous.comp (continuous_snd.comp continuous_fst)).prodMk
        continuous_snd).continuousOn
    · intro q hq
      exact ⟨hk q.1 hq.1,mem_univ _⟩
  obtain ⟨C,hC,hb⟩ := compact_frame_bound (isCompact_Icc.prod (isCompact_closedBall _ _))
    (fun q : ℝ × EC d => pathLogDetHessian g h p.index q.1 (coordinateEquiv d q.2))
    (fun q : ℝ × EC d => g.matrix p.index (coordinateEquiv d q.2))
    (fun q : ℝ × EC d => curvatureDiagonal (g.matrix p.index) (coordinateEquiv d q.2))
    ha hg (fun q hq => g.positive _ _ (hk q hq)) hR
    (fun q hq r v => curvatureDiagonal_smul ((g.smooth p.index).contDiffAt
      ((A.chart p.index).open_target.mem_nhds (hk q hq))) r v)
  refine ⟨C,hC,?_⟩
  intro t ht x hx B
  have hh := hb (t,A.euclideanChart p.index x) ⟨ht,ball_subset_closedBall hx.2⟩ B
  simpa only [ComplexAtlas.euclideanChart_apply,ContinuousLinearEquiv.apply_symm_apply] using hh
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
