import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSliceLocalization
import OAI.MathematicalPhysics.Boltzmann.Branching.SeedEscapeMeasure
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionWaitingCone
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalGlobalRenormalized

namespace OAI

section

/-! # Every nonempty physical history strictly advances collision time -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledEvent_ae_strict_time (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) :
    ∀ᵐ q ∂dampedDensityScaledEventKernel C b T ρ p, 0 ≤ q.1 ∧ q.1 < p.1 := by
  let A : Set PhysicalFlightState := {q | ¬(0 ≤ q.1 ∧ q.1 < p.1)}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledEventKernel C b T ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledEventKernel,Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral (ρ*C) p hF.lintegral_kernel]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [dampedDensityScaledCollision_lintegral _ _ _ _ _ hF,
    dampedMediumStateCollision_lintegral _ _ _ _ hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      ((physicalAdvance p s).1,((physicalAdvance p s).2.1,v)) = 0 := by
    apply indicator_of_notMem
    exact fun h => h ⟨sub_nonneg.mpr hs.2,sub_lt_self _ hs.1⟩
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem dampedBoundedDensityScaledEvent_ae_time_window (C : ℝ≥0) (b : BeamCoefficients)
    (T : ℝ) (ρ : ℝ≥0) {p q : PhysicalFlightState} (hq : boundedFlightCone p q) :
    ∀ᵐ r ∂dampedBoundedDensityScaledEvent C b T ρ q, T-p.1 < T-r.1 ∧ T-r.1 ≤ T := by
  change ∀ᵐ r ∂(dampedDensityScaledEventKernel C b T ρ q).restrict mediumVelocityBox, _
  filter_upwards [ae_restrict_of_ae (dampedDensityScaledEvent_ae_strict_time C b T ρ q)] with r hr
  exact ⟨sub_lt_sub_left (hr.2.trans_le hq.2.1) T,sub_le_self _ hr.1⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bounded portions of the entry velocities have one uniform late-box arrival time -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.EuclideanFlight
namespace BoltzmannNonuniqueness.ReferenceGeometry

def entryPhasePortion (κ ρ : ℝ) (n : ℕ) : Set WeakTime.Phase :=
  velocityPhaseBall κ ρ ∩ {p | ‖p‖ ≤ (n:ℝ)}

theorem entryPhasePortion_measurable (κ ρ : ℝ) (n : ℕ) :
    MeasurableSet (entryPhasePortion κ ρ n) :=
  (velocityPhaseBall_measurable κ ρ).inter (measurableSet_le measurable_id.norm measurable_const)

theorem entryPhasePortion_union (κ ρ : ℝ) :
    (⋃ n, entryPhasePortion κ ρ n) = velocityPhaseBall κ ρ := by
  ext p
  constructor
  · intro hp
    obtain ⟨n,hn⟩ := mem_iUnion.mp hp
    exact hn.1
  · intro hp
    obtain ⟨n,hn⟩ := exists_nat_gt ‖p‖
    exact mem_iUnion.mpr ⟨n,hp,hn.le⟩

theorem exists_positive_entryPortion {κ ρ : ℝ} (μ : Measure WeakTime.Phase)
    (hμ : 0 < μ (velocityPhaseBall κ ρ)) :
    ∃ n, 0 < μ (entryPhasePortion κ ρ n) := by
  apply exists_measure_pos_of_not_measure_iUnion_null
  rw [entryPhasePortion_union]
  exact ne_of_gt hμ

theorem entryPhasePortion_cutoff {κ ρ : ℝ} {n : ℕ} {p : WeakTime.Phase}
    (hp : p ∈ entryPhasePortion κ ρ n) : seedPhaseCutoff n p = 1 := by
  apply (seedPhaseBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall,dist_zero_right]
  dsimp [seedPhaseBump]
  have hb : ‖p‖ ≤ (n:ℝ) := hp.2
  linarith

theorem entryPhasePortion_eventually_lateBox {κ ρ d : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) (n : ℕ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t, T ≤ t → ∀ p ∈ entryPhasePortion κ ρ n,
      flight t p ∈ lateBox κ d t := by
  obtain ⟨T,_hT₀,hT,hbound⟩ := bounded_flight_lateBox (a := 0) (X := (n:ℝ)) hκ hd le_rfl
  refine ⟨T,hT,?_⟩
  intro t ht p hp
  have hv := velocityPhaseBall_subset_entry hκ.le hρd hρ₅ hp.1
  have hx := (norm_fst_le p).trans hp.2
  simpa only [sub_zero,flight] using hbound p.1 p.2 hx hv.1 hv.2 t ht

theorem positive_entryPortion_eventually_lateBox {κ ρ d : ℝ} (hκ : 0 < κ) (hd : 0 < d)
    (hρd : ρ ≤ d*κ/4) (hρ₅ : κ+ρ ≤ 5) (n : ℕ) (s : ℝ)
    (μ : ℝ → Measure WeakTime.Phase)
    (hμ : ∀ᵐ t ∂volume, s ≤ t → 0 < μ t (entryPhasePortion κ ρ n)) :
    ∃ T : ℝ, 0 < T ∧ ∀ᵐ t ∂volume, T ≤ t → 0 < μ t (flight t ⁻¹' lateBox κ d t) := by
  obtain ⟨T,hT,hbound⟩ := entryPhasePortion_eventually_lateBox hκ hd hρd hρ₅ n
  refine ⟨max s T,hT.trans_le (le_max_right _ _),?_⟩
  filter_upwards [hμ] with t ht
  intro htt
  exact (ht ((le_max_left _ _).trans htt)).trans_le
    (measure_mono (hbound t ((le_max_right _ _).trans htt)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
