import Mathlib
import OAI.Geometry.PrescribedPotential.KaehlerClosedDerivatives
import OAI.Geometry.PrescribedPotential.ParametrixAtlas

namespace OAI

/-! Coordinate Balls. -/

section

 

noncomputable section
open Set Metric Filter Topology MeasureTheory
open scoped ContDiff
namespace Anticanonical.SourceSmooth
open EllipticKernel
local instance coordinateBallRealIP (d : ℕ) : InnerProductSpace ℝ (EC d) :=
  InnerProductSpace.rclikeToReal ℂ (EC d)
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

structure CoordinateBall (A : ComplexAtlas d X) where
  index : Fin A.count
  center : EC d
  radius : ℝ
  radius_pos : 0 < radius
  closure_sub : closedBall center (4*radius) ⊆ (A.euclideanChart index).target

namespace CoordinateBall
variable (p : CoordinateBall A)
def source : Set X := (A.euclideanChart p.index).source ∩
  (A.euclideanChart p.index) ⁻¹' ball p.center p.radius

lemma ball_sub : ball p.center p.radius ⊆ (A.euclideanChart p.index).target := by
  apply subset_trans _ p.closure_sub
  exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith [p.radius_pos])))

lemma isOpen_source : IsOpen p.source :=
  (A.euclideanChart p.index).isOpen_inter_preimage isOpen_ball

lemma source_nonempty : p.source.Nonempty := by
  have hc : p.center ∈ (A.euclideanChart p.index).target :=
    p.ball_sub (mem_ball_self p.radius_pos)
  refine ⟨(A.euclideanChart p.index).symm p.center,
    (A.euclideanChart p.index).symm.mapsTo hc, ?_⟩
  change A.euclideanChart p.index ((A.euclideanChart p.index).symm p.center) ∈ ball p.center p.radius
  rw [(A.euclideanChart p.index).right_inv hc]
  exact mem_ball_self p.radius_pos

lemma exists_at (x : X) : ∃ p : CoordinateBall A, x ∈ p.source := by
  obtain ⟨i, hi⟩ := A.covers x
  let e := A.euclideanChart i
  have hxe : x ∈ e.source := by simpa [e] using hi
  have hxt : e x ∈ e.target := e.mapsTo hxe
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (e.open_target.mem_nhds hxt)
  refine ⟨⟨i, e x, r/4, by positivity, ?_⟩, hxe, ?_⟩
  · convert hsub using 1; ring_nf
  · exact mem_ball_self (by positivity)

theorem finite_cover [CompactSpace X] :
    ∃ S : Finset (CoordinateBall A), ∀ x, ∃ p ∈ S, x ∈ p.source := by
  classical
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun p : CoordinateBall A => p.source) (fun p => p.isOpen_source) (by
      intro x _
      obtain ⟨p, hp⟩ := exists_at (A := A) x
      exact mem_iUnion.mpr ⟨p, hp⟩)
  refine ⟨S, fun x => ?_⟩
  obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp (hS (mem_univ x))
  exact ⟨q, hq, hxq⟩

section Measure
variable [MeasurableSpace X] [BorelSpace X]

def measure : Measure X :=
  Measure.map (A.euclideanChart p.index).symm (volume.restrict (ball p.center p.radius))

instance : IsFiniteMeasure p.measure := by
  have : IsFiniteMeasure (volume.restrict (ball p.center p.radius)) :=
    isFiniteMeasure_restrict.mpr isBounded_ball.measure_lt_top.ne
  unfold measure
  infer_instance

lemma symm_aemeasurable : AEMeasurable (A.euclideanChart p.index).symm
    (volume.restrict (ball p.center p.radius)) :=
  ((A.euclideanChart p.index).continuousOn_symm.mono p.ball_sub).aemeasurable
    isOpen_ball.measurableSet

lemma integral_measure (f : X → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂p.measure) =
      ∫ z in ball p.center p.radius, f ((A.euclideanChart p.index).symm z) := by
  exact integral_map p.symm_aemeasurable hf.aestronglyMeasurable

lemma measure_open_pos {U : Set X} (hU : IsOpen U) (hnear : (p.source ∩ U).Nonempty) :
    0 < p.measure.real U := by
  have he : ((A.euclideanChart p.index).symm ⁻¹' U) ∩ ball p.center p.radius =
      ball p.center p.radius ∩
        ((A.euclideanChart p.index).target ∩ (A.euclideanChart p.index).symm ⁻¹' U) := by
    ext z
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hu, hz⟩; exact ⟨hz, p.ball_sub hz, hu⟩
    · rintro ⟨hz, _, hu⟩; exact ⟨hu, hz⟩
  have ho : IsOpen (((A.euclideanChart p.index).symm ⁻¹' U) ∩ ball p.center p.radius) := by
    rw [he]
    exact isOpen_ball.inter ((A.euclideanChart p.index).symm.isOpen_inter_preimage hU)
  have hn : (((A.euclideanChart p.index).symm ⁻¹' U) ∩ ball p.center p.radius).Nonempty := by
    obtain ⟨x, hx, hxu⟩ := hnear
    refine ⟨A.euclideanChart p.index x, ?_, hx.2⟩
    simpa only [mem_preimage, (A.euclideanChart p.index).left_inv hx.1] using hxu
  have hm : 0 < p.measure U := by
    change 0 < Measure.map _ _ U
    rw [Measure.map_apply_of_aemeasurable p.symm_aemeasurable hU.measurableSet,
      Measure.restrict_apply' isOpen_ball.measurableSet]
    exact ho.measure_pos volume hn
  exact ENNReal.toReal_pos hm.ne' (measure_ne_top p.measure U)
end Measure
end CoordinateBall
end Anticanonical.SourceSmooth

end
end

end OAI
