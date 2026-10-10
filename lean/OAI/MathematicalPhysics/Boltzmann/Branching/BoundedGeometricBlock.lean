import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBoundedEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumEndpointTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.ScaledBoundedEvent
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantPowers
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Jets.BeamNormalOutgoing
import OAI.MathematicalPhysics.Boltzmann.Jets.GeometricAnnularFrequency

namespace OAI

section

/-! # The finite-speed cone of the velocity-truncated physical histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def boundedFlightCone (p q : PhysicalFlightState) : Prop :=
  0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.2‖ ≤ 6 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1)

theorem boundedFlightCone_measurable (p : PhysicalFlightState) :
    MeasurableSet {q | boundedFlightCone p q} := by
  have hv : Measurable (fun q : PhysicalFlightState => ‖q.2.2‖) := by fun_prop
  have hx : Measurable (fun q : PhysicalFlightState => ‖q.2.1-p.2.1‖) := by fun_prop
  have ht : Measurable (fun q : PhysicalFlightState => 6*(p.1-q.1)) := by fun_prop
  unfold boundedFlightCone
  exact (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_fst measurable_const).inter
      ((measurableSet_le hv measurable_const).inter (measurableSet_le hx ht)))

theorem boundedFlightCone_refl {p : PhysicalFlightState} (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6) :
    boundedFlightCone p p := by
  exact ⟨ht,le_rfl,hv,by simp⟩

theorem boundedFlightCone_trans {p q r : PhysicalFlightState}
    (hpq : boundedFlightCone p q) (hqr : boundedFlightCone q r) : boundedFlightCone p r := by
  refine ⟨hqr.1,hqr.2.1.trans hpq.2.1,hqr.2.2.1,?_⟩
  calc
    ‖r.2.1-p.2.1‖ = ‖(r.2.1-q.2.1)+(q.2.1-p.2.1)‖ := by rw [sub_add_sub_cancel]
    _ ≤ ‖r.2.1-q.2.1‖+‖q.2.1-p.2.1‖ := norm_add_le _ _
    _ ≤ 6*(q.1-r.1)+6*(p.1-q.1) := add_le_add hqr.2.2.2 hpq.2.2.2
    _ = 6*(p.1-r.1) := by ring

theorem boundedFlightCone_step {p : PhysicalFlightState} {s : ℝ} {v : V}
    (hs : s ∈ Ioc 0 p.1) (hp : ‖p.2.2‖ ≤ 6) (hv : ‖v‖ ≤ 6) :
    boundedFlightCone p (p.1-s,(p.2.1+s • p.2.2,v)) := by
  refine ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le,hv,?_⟩
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hs.1]
  have hm := mul_le_mul_of_nonneg_left hp hs.1.le
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Actual bounded physical events stay in their finite-speed cone almost everywhere -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedDensityScaledEvent_ae_geometry (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂dampedDensityScaledEventKernel C b endTime ρ p,
      0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1) := by
  let A : Set PhysicalFlightState :=
    {q | ¬(0 ≤ q.1 ∧ q.1 ≤ p.1 ∧ ‖q.2.1-p.2.1‖ ≤ 6*(p.1-q.1))}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hF : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [ae_iff]
  change dampedDensityScaledEventKernel C b endTime ρ p A = 0
  rw [← lintegral_indicator_one hA,dampedDensityScaledEventKernel,
    Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral (ρ*C) p hF.lintegral_kernel]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [dampedDensityScaledCollision_lintegral _ _ _ _ _ hF,
    dampedMediumStateCollision_lintegral _ _ _ _ hF]
  have hz (v : V) : A.indicator (1 : PhysicalFlightState → ℝ≥0∞)
      ((physicalAdvance p s).1,((physicalAdvance p s).2.1,v)) = 0 := by
    have hc := boundedFlightCone_step hs hp (show ‖(0:V)‖ ≤ 6 by simp)
    apply indicator_of_notMem
    exact fun h => h ⟨hc.1,hc.2.1,hc.2.2.2⟩
  simp only [hz,lintegral_zero,mul_zero,Pi.zero_apply]

theorem dampedBoundedDensityScaledEvent_ae_cone (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂dampedBoundedDensityScaledEvent C b endTime ρ p, boundedFlightCone p q := by
  change ∀ᵐ q ∂(dampedDensityScaledEventKernel C b endTime ρ p).restrict mediumVelocityBox,
    boundedFlightCone p q
  filter_upwards [ae_restrict_of_ae (dampedDensityScaledEvent_ae_geometry C b endTime ρ p hp),
    ae_restrict_mem mediumVelocityBox_measurable] with q hq hv
  exact ⟨hq.1,hq.2.1,hv,hq.2.2⟩

theorem dampedBoundedDensityScaledEvent_pow_ae_cone (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    (ht : 0 ≤ p.1) (hp : ‖p.2.2‖ ≤ 6) :
    ∀ᵐ q ∂((dampedBoundedDensityScaledEvent C b endTime ρ)^n) p, boundedFlightCone p q := by
  induction n with
  | zero =>
    change ∀ᵐ q ∂Measure.dirac p, boundedFlightCone p q
    exact (ae_dirac_iff (boundedFlightCone_measurable p)).mpr (boundedFlightCone_refl ht hp)
  | succ n ih =>
    rw [pow_succ']
    apply Kernel.ae_comp_of_ae_ae (boundedFlightCone_measurable p)
    filter_upwards [ih] with q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b endTime ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A nonzero density has a bounded positive portion away from the velocity axis -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

def seedPortion (n : ℕ) : Set (Velocity × Velocity) :=
  {p | ‖p.1‖ ≤ n ∧ ‖p.2‖ ≤ n ∧ 1/((n : ℝ)+1) ≤ ‖transverse p.2‖}

theorem seedPortion_measurable (n : ℕ) : MeasurableSet (seedPortion n) := by
  unfold seedPortion
  measurability

theorem seedPortion_iUnion :
    (⋃ n : ℕ, seedPortion n) = {p : Velocity × Velocity | transverse p.2 ≠ 0} := by
  ext p
  constructor
  · intro hp
    obtain ⟨n,hn⟩ := mem_iUnion.mp hp
    have hpos : 0 < (1 : ℝ)/((n : ℝ)+1) := by positivity
    exact norm_pos_iff.mp (hpos.trans_le hn.2.2)
  · intro hp
    have hr : 0 < ‖transverse p.2‖ := norm_pos_iff.mpr hp
    obtain ⟨n,hn⟩ := exists_nat_gt (max (max ‖p.1‖ ‖p.2‖) (1/‖transverse p.2‖))
    apply mem_iUnion.mpr
    refine ⟨n,(le_max_left _ _).trans (le_max_left _ _ |>.trans hn.le),
      (le_max_right _ _).trans (le_max_left _ _ |>.trans hn.le),?_⟩
    have hdiv : 1/‖transverse p.2‖ ≤ (n : ℝ) := (le_max_right _ _).trans hn.le
    have hmul := (div_le_iff₀ hr).mp hdiv
    apply (div_le_iff₀ (show 0 < (n : ℝ)+1 by positivity)).mpr
    nlinarith

theorem exists_positive_seedPortion (μ : Measure (Velocity × Velocity))
    (hac : μ ≪ volume) (hne : μ ≠ 0) : ∃ n : ℕ, 0 < μ (seedPortion n) := by
  apply exists_measure_pos_of_not_measure_iUnion_null
  have hfull : ∀ᵐ p ∂μ, p ∈ ⋃ n : ℕ, seedPortion n := by
    apply hac.ae_le
    rw [seedPortion_iUnion,Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae SheetApplication.ae_transverse_ne_zero
  have hc : μ (⋃ n : ℕ, seedPortion n)ᶜ = 0 := hfull
  intro hzero
  apply hne
  apply Measure.measure_univ_eq_zero.mp
  apply le_antisymm _ bot_le
  calc
    μ univ = μ ((⋃ n : ℕ, seedPortion n) ∪ (⋃ n : ℕ, seedPortion n)ᶜ) := by
      rw [union_compl_self]
    _ ≤ μ (⋃ n : ℕ, seedPortion n)+μ (⋃ n : ℕ, seedPortion n)ᶜ := measure_union_le _ _
    _ = 0 := by rw [hzero,hc,zero_add]

end BoltzmannNonuniqueness

end

end

section

/-! # Bounded-velocity branching growth from the visited cylinder -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem uniform_bounded_local_beam_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-z.1‖ ≤ 6*A → BeamNear b ε y) →
      (6 : ℝ≥0∞) < boundedMediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_bounded_perturbed_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₁,hε₁,hblock⟩ := hgrowth T hT
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨N,min ε₁ (1/L),lt_min hε₁ (one_div_pos.mpr hL),?_⟩
  intro ε hε A hA z b endTime hnear
  apply hblock ε ⟨hε.1,hε.2.trans (min_le_left _ _)⟩ A hA z b endTime
  intro n hn a ha
  have hnL : (n:ℝ) ≤ L := (Nat.cast_le.mpr hn.le).trans (le_add_of_nonneg_right (by norm_num))
  have hbudget : (n:ℝ)*ε ≤ 1 :=
    (mul_le_mul_of_nonneg_right hnL hε.1).trans (by
      have hh := (le_div_iff₀ hL).mp (hε.2.trans (min_le_right _ _))
      simpa only [mul_comm] using hh)
  exact wordNearby_from_start b endTime A z hε.1 (hA₀.le.trans hA.1) hnear n hbudget a ha

theorem uniform_bounded_physical_beam_block {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ v : RetainedState,
      ∀ (b : BeamCoefficients) (ρ t₀ : ℝ) (x₀ : V), 0 < ρ →
      (∀ p : ℝ × V, p.1 ∈ Icc t₀ (t₀+A/ρ) → ‖p.2-x₀‖ ≤ 6*A/ρ → BeamNear b ε p) →
      (6 : ℝ≥0∞) < boundedMediumBlockMass (b.normalized ρ t₀ x₀) A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hgrowth⟩ := uniform_bounded_local_beam_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₀,hε₀,hblock⟩ := hgrowth T hT
  refine ⟨N,ε₀,hε₀,?_⟩
  intro ε hε A hA v b ρ t₀ x₀ hρ hnear
  apply hblock ε hε A hA (0,v) (b.normalized ρ t₀ x₀) A
  intro p hp hx
  exact normalized_beam_near b hρ x₀ hnear p (by simpa using hp) (by simpa using hx)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed time-window representations of the bounded event histories -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem boundedMediumEventKernel_eq_physical (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    boundedMediumEventKernel b endTime T p = boundedPhysicalEvent b endTime p := by
  rw [boundedMediumEventKernel,Kernel.restrict_apply,
    boundedPhysicalEvent,Kernel.restrict_apply,mediumEventKernel_eq_comp b endTime p hT]

theorem boundedMediumEventKernel_remaining_le (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ∀ᵐ q ∂boundedMediumEventKernel b endTime T p, q.1 ≤ p.1 := by
  rw [boundedMediumEventKernel,Kernel.restrict_apply]
  exact ae_restrict_of_ae (mediumEventKernel_remaining_le b endTime p hT)

theorem boundedMediumEventKernel_pow_eq_physical (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    ((boundedMediumEventKernel b endTime T)^n) p = ((boundedPhysicalEvent b endTime)^n) p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hpow (L : Kernel PhysicalFlightState PhysicalFlightState) :
        L^(n+1) = (L^n) ∘ₖ L := by
      simpa only [pow_one] using Kernel.pow_add L n 1
    rw [hpow,hpow,Kernel.comp_apply,Kernel.comp_apply]
    calc
      (boundedMediumEventKernel b endTime T p).bind ((boundedMediumEventKernel b endTime T)^n) =
          (boundedMediumEventKernel b endTime T p).bind ((boundedPhysicalEvent b endTime)^n) := by
        apply Measure.bind_congr_right
        filter_upwards [boundedMediumEventKernel_remaining_le b endTime p hT] with q hq
        exact ih q (hq.trans hT)
      _ = _ := by rw [boundedMediumEventKernel_eq_physical b endTime p hT]

theorem densityScaled_bounded_history_map (b : BeamCoefficients) {ρ : ℝ} (hρ : 0 < ρ)
    (t₀ endTime : ℝ) (x₀ : V) (n : ℕ) (p : PhysicalFlightState) {T : ℝ} (hT : ρ*p.1 ≤ T) :
    (((boundedDensityScaledEvent b endTime (Real.toNNReal ρ))^n) p).map
      (flightScaleEquiv ρ hρ.ne' x₀) =
      ((boundedMediumEventKernel (b.normalized ρ t₀ x₀) (ρ*(endTime-t₀)) T)^n)
        (flightScaleEquiv ρ hρ.ne' x₀ p) := by
  rw [boundedDensityScaledEvent_pow_map b hρ t₀ endTime x₀ n p,
    boundedMediumEventKernel_pow_eq_physical _ _ _ _ hT]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Localizing a bounded physical history outside its reachable cone changes no endpoint -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedBoundedDensityScaledEvent_localization (C : ℝ≥0) (b : BeamCoefficients)
    (endTime : ℝ) (ρ : ℝ≥0) (p : PhysicalFlightState)
    (ht : 0 ≤ p.1) (hv : ‖p.2.2‖ ≤ 6)
    {D E : Set PhysicalFlightState} [DecidablePred (· ∈ D)]
    (hD : MeasurableSet D) (hE : MeasurableSet E)
    (hDc : ∀ q, boundedFlightCone p q → q ∈ D)
    (hEc : ∀ q, boundedFlightCone p q → q ∈ E) (n : ℕ) :
    ((dampedBoundedDensityScaledEvent C b endTime ρ)^n) p =
      ((Kernel.piecewise hD ((dampedBoundedDensityScaledEvent C b endTime ρ).restrict hE) 0)^n) p := by
  classical
  have hinv : ∀ q, boundedFlightCone p q →
      ∀ᵐ r ∂dampedBoundedDensityScaledEvent C b endTime ρ q, boundedFlightCone p r := by
    intro q hq
    filter_upwards [dampedBoundedDensityScaledEvent_ae_cone C b endTime ρ q hq.2.2.1] with r hr
    exact boundedFlightCone_trans hq hr
  apply kernel_pow_eq_on_invariant _ _ {q | boundedFlightCone p q} hinv _ n p
    (boundedFlightCone_refl ht hv)
  intro q hq
  rw [Kernel.piecewise_apply,ite_eq_left (hDc q hq),Kernel.restrict_apply]
  apply (Measure.restrict_eq_self_of_ae_mem ?_).symm
  filter_upwards [hinv q hq] with r hr
  exact hEc r hr

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A bounded-velocity growing block for the actual geometric cold coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.ReferenceGeometry BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.GeometricBackground

theorem geometric_bounded_block_growth {d κ C : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) (hC : 1 ≤ C) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T →
      ∃ N : ℕ, ∃ ε γ₀ : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 < γ₀ ∧
      ∀ {θ η r α γ K t₀ A : ℝ}, (hθ : 0 < θ) →
      0 < η → η ≤ Real.log (1+ε/20) → 0 < r →
      (hα : 0 ≤ α) → α ≤ ε → (hγ : 0 ≤ γ) → γ ≤ γ₀ →
      0 < K → 480*T ≤ ε*K → 0 ≤ t₀ → t₀ ≤ C*r/2 → A ∈ Icc A₀ T →
      ∀ (x₀ : Velocity) (v : RetainedState), ‖transverse x₀‖ = r → |axial x₀| ≤ C*r/2 →
      (6 : ℝ≥0∞) < boundedMediumBlockMass
        ((beamCoefficients hθ hα hγ η r).normalized (K/(4*r)) t₀ x₀)
        A T (A,(0,v)) κ d N := by
  obtain ⟨A₀,hA₀,hblock⟩ := uniform_bounded_physical_beam_block hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,ε₀,hε₀,hgrowth⟩ := hblock T hT
  let ε := min ε₀ (1/4:ℝ)
  have hε : 0 < ε := lt_min hε₀ (by norm_num)
  have hεsmall : ε ≤ 1/4 := min_le_right _ _
  obtain ⟨γ₀,hγ₀,hnear⟩ := beam_near_on_cylinder hε (by linarith) hC
  refine ⟨N,ε,γ₀,hε,hεsmall,hγ₀,?_⟩
  intro θ η r α γ K t₀ A hθ hη hηsmall hr hα hαε hγ hγsmall hK hlarge ht₀ ht₀C hA x₀ v hx₀ hz₀
  have hρ : 0 < K/(4*r) := by positivity
  have hbudget : 480*A ≤ ε*K := (mul_le_mul_of_nonneg_left hA.2 (by norm_num)).trans hlarge
  have hshort := cylinder_small_of_density_scale hK hr hbudget
  apply hgrowth ε ⟨hε.le,min_le_left _ _⟩ A hA v (beamCoefficients hθ hα hγ η r)
    (K/(4*r)) t₀ x₀ hρ
  exact hnear hθ hη hηsmall hr hα hαε hγ hγsmall hρ ht₀ ht₀C hshort x₀ hx₀ hz₀

end BoltzmannNonuniqueness.GeometricBackground

end

end

end OAI
