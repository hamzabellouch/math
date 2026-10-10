import OAI.Geometry.RCD.Metric.MovingPointedLimitApproximation

namespace OAI

/-! # Pointed precompactness with arbitrary moving centers

The CD finite-net bound is uniform in the center. The same countable
distance construction therefore applies to any sequence of centers and
scales whose rescaled lower curvature is bounded below by minus one.
-/

open Set Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.moving_pointed_compactness {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n) (p : ℕ → X) (r : ℕ → ℝ)
    (hr : ∀ i, 0<r i) (hcurv : ∀ i, -1≤K*(r i)^2) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ (Y : Type u) (dY : MetricSpace Y),
      letI := dY
      ∃ (_ : ProperSpace Y) (q : Y), PointedSequenceConverges (p∘phi) q (r∘phi) := by
  obtain ⟨s⟩ := hX.movingRescalingNetFamily hn p r hr hcurv
  obtain ⟨phi,hphi,d,hconv⟩ := s.exists_limit hr
  let := d
  let Y₀ := UniformSpace.Completion s.Index
  let : ProperSpace Y₀ := s.completion_proper phi hr hconv
  let Y := ULift.{u} Y₀
  let e : Y₀ ≃ᵢ Y := {
    toEquiv := Equiv.ulift.symm
    isometry_toFun := isometry_iff_dist_eq.mpr (fun _ _ => rfl) }
  have hproper : ProperSpace Y := by
    refine ⟨fun z R => ?_⟩
    have hball : closedBall z R=e '' closedBall (e.symm z) R := by
      ext w
      constructor
      · intro hw
        exact ⟨e.symm w,by simpa only [mem_closedBall,e.symm.dist_eq] using hw,e.apply_symm_apply w⟩
      · rintro ⟨w,hw,rfl⟩
        simpa only [mem_closedBall,← e.dist_eq w (e.symm z),e.apply_symm_apply] using hw
    rw [hball]
    exact (isCompact_closedBall (e.symm z) R).image e.continuous
  refine ⟨phi,hphi,Y,inferInstance,hproper,e (none : s.Index),?_⟩
  intro R hR ε hε
  filter_upwards [s.pointedSequenceConverges phi hr hconv R hR ε hε] with i hi
  obtain ⟨f,hf⟩ := hi
  exact ⟨fun x => e (f x),hf.postcomp_isometry e⟩

end RegularPointCoordinates

end

end OAI
