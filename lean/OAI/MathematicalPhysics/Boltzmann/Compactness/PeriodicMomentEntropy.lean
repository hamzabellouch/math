import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedMildBalance
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicFiniteMild
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # Integrable undamped sources of the actual periodic cutoff solutions -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.collision (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  S.source z-lossBound N*S.density z

def BoundedCutoffSolution.characteristicSource (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) : ℝ :=
  S.collision (z.1,TorusFlight.flight z.1 z.2)

theorem BoundedCutoffSolution.collision_eq (S : BoundedCutoffSolution N T f₀) (z : ℝ × Phase) :
    S.collision z = gain N (fun p => S.density (z.1,p)) z.2-
      loss N (fun p => S.density (z.1,p)) z.2 := by
  unfold collision source positiveSource
  ring

theorem BoundedCutoffSolution.collision_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.collision := S.source_measurable.sub (measurable_const.mul S.measurable)

theorem BoundedCutoffSolution.collision_support (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (z : ℝ × Phase) (hz : N < ‖z.2.2‖) : S.collision z = 0 := by
  rw [S.collision_eq,gain_zero_of_velocity hN _ z.2 hz,loss_zero_of_velocity hN _ z.2 hz,sub_self]

theorem BoundedCutoffSolution.collision_bounded (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z, |S.collision z| ≤ D := by
  obtain ⟨C,hC,hCb⟩ := S.source_bounded hN
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hL : 0 ≤ lossBound N := by unfold lossBound; positivity
  refine ⟨C+lossBound N*B,by positivity,?_⟩
  intro z
  calc
    _ ≤ |S.source z|+|lossBound N*S.density z| := abs_sub _ _
    _ = |S.source z|+lossBound N*S.density z := by
      rw [abs_of_nonneg (mul_nonneg hL (S.nonnegative z))]
    _ ≤ C+lossBound N*B := by
      gcongr
      · exact hCb z
      · exact hB z

theorem BoundedCutoffSolution.weighted_collision_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) :
    Integrable (fun z : ℝ × Phase => ψ z.2.2*S.collision z)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  obtain ⟨D,hD,hDb⟩ := S.collision_bounded hN
  have hC : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ 0 (by simpa using hN.le))
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let g : (ℝ × Position) × Velocity → ℝ := fun p => ψ p.2*S.collision (p.1.1,(p.1.2,p.2))
  have hgm : Measurable g :=
    (hψm.comp measurable_snd).mul (S.collision_measurable.comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)))
  have hgb (p : (ℝ × Position) × Velocity) : |g p| ≤ C*D := by
    dsimp only [g]
    by_cases hp : N < ‖p.2‖
    · rw [S.collision_support hN.le (p.1.1,(p.1.2,p.2)) hp,mul_zero,abs_zero]
      positivity
    · rw [abs_mul]
      exact mul_le_mul (hψ p.2 (le_of_not_gt hp)) (hDb (p.1.1,(p.1.2,p.2))) (abs_nonneg _) hC
  have hgs (p : (ℝ × Position) × Velocity) (hp : N < ‖p.2‖) : g p = 0 := by
    dsimp only [g]
    rw [S.collision_support hN.le (p.1.1,(p.1.2,p.2)) hp,mul_zero]
  have hg : Integrable g (μ.prod volume) := bounded_velocity_integrable (μ := μ) (N := N) hgm hgb hgs
  have hr := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable hg
  change Integrable (fun z : ℝ × Phase => ψ z.2.2*S.collision z)
    ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod (volume : Measure Velocity))) at hr
  simpa only [Measure.volume_eq_prod] using hr

theorem BoundedCutoffSolution.characteristicSource_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.characteristicSource := S.collision_measurable.comp
      (measurable_fst.prodMk TorusFlight.measurable_flight)

theorem BoundedCutoffSolution.weighted_characteristic_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) :
    Integrable (fun z : ℝ × Phase => ψ z.2.2*S.characteristicSource z)
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) :=
  (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable
    (S.weighted_collision_integrable hN ψ hψm hψ)

theorem BoundedCutoffSolution.eulerianProfile_eq (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    TorusFlight.eulerianProfile (volume.restrict (Icc 0 T)) f₀ S.characteristicSource t p =
      S.density (t,p) := by
  unfold TorusFlight.eulerianProfile TorusFlight.characteristicProfile
  rw [Published.timePrimitive_eq_interval ht]
  have he := S.characteristic_integral hN ht (TorusFlight.flight (-t) p)
  rw [TorusFlight.neg_flight] at he
  exact he.symm

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time moment conservation of the constructed supported approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.weighted_density_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C) (t : ℝ) :
    Integrable (fun p : Phase => ψ p.2*S.density (t,p)) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hB0 : 0 ≤ B := (S.nonnegative (0,0)).trans (hB (0,0))
  have hC : 0 ≤ C := (abs_nonneg (ψ 0)).trans (hψ 0 (by simpa using hN))
  rw [Measure.volume_eq_prod]
  apply bounded_velocity_integrable (A := C*B)
  · exact (hψm.comp measurable_snd).mul (S.measurable.comp (measurable_const.prodMk measurable_id))
  · intro p
    by_cases hp : N < ‖p.2‖
    · rw [S.support (t,p) hp,mul_zero,abs_zero]
      positivity
    · rw [abs_mul,abs_of_nonneg (S.nonnegative (t,p))]
      exact mul_le_mul (hψ _ (le_of_not_gt hp)) (hB (t,p)) (S.nonnegative (t,p)) hC
  · intro p hp
    rw [S.support (t,p) hp,mul_zero]

theorem BoundedCutoffSolution.weighted_collision_zero (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) (t : ℝ) :
    (∫ p : Phase, ψ p.2*S.collision (t,p)) = 0 := by
  have hm : Measurable (fun p : Phase => S.density (t,p)) :=
    S.measurable.comp (measurable_const.prodMk measurable_id)
  have hn (p : Phase) : 0 ≤ S.density (t,p) := S.nonnegative (t,p)
  have hw (p : Phase) (hp : ‖p.2‖ ≤ N) : |ψ p.2| ≤ C := hψ p.2 hp
  have hi := regularized_test_marginals (μ := (volume : Measure Position)) hN hm hn
    (hψm.comp measurable_snd) hw
  have he := regularized_test_invariant (μ := (volume : Measure Position)) hN hm hn
    (hψm.comp measurable_snd) hw hj
  dsimp only [Function.comp_def] at hi he
  simp_rw [S.collision_eq,mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2.1,he,sub_self]

theorem BoundedCutoffSolution.weighted_characteristic_zero (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) (t : ℝ) :
    (∫ p : Phase, ψ p.2*S.characteristicSource (t,p)) = 0 :=
  (TorusFlight.integral_flight (fun p : Phase => ψ p.2*S.collision (t,p)) t).trans
    (S.weighted_collision_zero hN ψ hψm hψ hj t)

theorem BoundedCutoffSolution.moment_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) (ψ : Velocity → ℝ) (hψm : Measurable ψ) {C : ℝ}
    (hψ : ∀ v, ‖v‖ ≤ N → |ψ v| ≤ C)
    (hj : ∀ z : (Position × (Velocity × Velocity)) × Sphere,
      collisionJump (fun p : Phase => ψ p.2) z = 0) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, ψ p.2*S.density (t,p)) = ∫ p : Phase, ψ p.2*f₀ p := by
  have hm : Measurable (fun z : ℝ × Phase => ψ z.2.2*S.characteristicSource z) :=
    (hψm.comp measurable_snd.snd).mul S.characteristicSource_measurable
  have hfi := S.weighted_density_integrable hN.le ψ hψm hψ 0
  have he : (fun p => ψ p.2*S.density (0,p)) = (fun p => ψ p.2*f₀ p) := by
    funext p
    rw [S.initial hT]
  rw [he] at hfi
  have h := TorusFlight.velocity_weighted_profile_balance f₀ S.characteristicSource ψ hm
    (S.weighted_characteristic_integrable hN ψ hψm hψ) hfi t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, ψ p.2*S.characteristicSource (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with s
    rw [S.weighted_characteristic_zero hN ψ hψm hψ hj s]
    split_ifs <;> rfl
  rw [hz,add_zero] at h
  calc
    _ = ∫ p : Phase, ψ p.2*TorusFlight.eulerianProfile (volume.restrict (Icc 0 T))
        f₀ S.characteristicSource t p := by
      apply integral_congr_ae
      filter_upwards [] with p
      rw [S.eulerianProfile_eq hN ht]
    _ = _ := h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The approximate entropy-production estimate in physical coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.kinetic_collision (S : BoundedCutoffSolution N T f₀)
    (p : (ℝ × Position) × Velocity) :
    collisionOperator N (fun p : (ℝ × Position) × Velocity => S.density (p.1.1,(p.1.2,p.2))) p =
      S.collision (p.1.1,(p.1.2,p.2)) := by
  rw [S.collision_eq]
  rfl

theorem BoundedCutoffSolution.log_collision_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {B δ : ℝ} (hB : 0 ≤ B) (hSb : ∀ z, S.density z ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    Integrable (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
      ((volume.restrict (Icc 0 t)).prod volume) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 t)).prod volume
  let f : (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))
  have hfm : Measurable f := S.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hm : Measurable (fun p : (ℝ × Position) × Velocity => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hψ := ((gaussianShift_measurable δ hfm).div hm).log
  have hi := collisionOperator_test_integrable (μ := μ) hN hfm
    (fun p => S.nonnegative (p.1.1,(p.1.2,p.2))) hψ
    (fun p hp => log_regularization_bound hN.le hB hδ hδ1 (S.nonnegative _)
      (hSb _) p.2 hp)
  dsimp only [f] at hi
  simp only [S.kinetic_collision] at hi
  have hr := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).symm.integrable_comp_of_integrable hi
  change Integrable (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
    ((volume.restrict (Icc 0 t)).prod volume) at hr
  exact hr

theorem BoundedCutoffSolution.entropy_production_bound (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {B δ : ℝ} (hB : 0 ≤ B) (hSb : ∀ z, S.density z ≤ B)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (t : ℝ) :
    (∫ z : ℝ × Phase, Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z
      ∂(volume.restrict (Icc 0 t)).prod volume) ≤
      entropyErrorCoefficient ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N*
        δ*(|Real.log δ|+logRegularizationConstant N B) := by
  let f : (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))
  have hfm : Measurable f := S.measurable.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h := nonnegative_entropy_production_bound
    (μ := (volume.restrict (Icc 0 t)).prod (volume : Measure Position)) hN hB hδ hδ1 hfm
    (fun p => S.nonnegative (p.1.1,(p.1.2,p.2))) (fun p => hSb _)
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
  rw [← he]
  dsimp only [f] at h
  simp only [S.kinetic_collision,gaussianShift] at h
  convert h using 1
  congr 1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrating the entropy balance of the constructed cutoff trajectories -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.endpoint_entropy_integrable (S : BoundedCutoffSolution N T f₀)
    {δ : ℝ} (hδ : δ ∈ Icc (0:ℝ) 1) (t : ℝ) :
    Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p))) := by
  obtain ⟨B,hB⟩ := S.bounded
  rw [Measure.volume_eq_prod]
  exact regularizedEntropy_integrable hδ
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.integrated_entropy_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t δ : ℝ} (ht : t ∈ Icc 0 T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) =
    ∫ z : ℝ × Phase, Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z
      ∂(volume.restrict (Icc 0 t)).prod volume := by
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have hi := S.log_collision_integrable hN hB hSb hδ hδ1 t
  have halong := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 t))).integrable_comp_of_integrable hi
  have htE := S.endpoint_entropy_integrable ⟨hδ.le,hδ1⟩ t
  have htEa := (TorusFlight.flight_measurePreserving t).integrable_comp_of_integrable htE
  have h0E : Integrable (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
    simpa only [S.initial hT] using S.endpoint_entropy_integrable ⟨hδ.le,hδ1⟩ 0
  have hpath (p : Phase) :
      regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,TorusFlight.flight t p))-
        regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) =
      ∫ r, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
        S.collision (r,TorusFlight.flight r p) ∂volume.restrict (Icc 0 t) := by
    have h := (S.entropy_path_balance hN ht hδ p).symm
    rw [intervalIntegral.integral_of_le ht.1,← integral_Icc_eq_integral_Ioc] at h
    exact h
  calc
    _ = (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ
          (S.density (t,TorusFlight.flight t p)))-
        (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
      rw [← TorusFlight.integral_flight
        (fun p => regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p))) t]
      rfl
    _ = ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ
          (S.density (t,TorusFlight.flight t p))-
        regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p) :=
      (integral_sub htEa h0E).symm
    _ = ∫ p, ∫ r, Real.log ((S.density (r,TorusFlight.flight r p)+δ*maxwellian p.2)/maxwellian p.2)*
        S.collision (r,TorusFlight.flight r p) ∂volume.restrict (Icc 0 t) :=
      integral_congr_ae (Filter.Eventually.of_forall hpath)
    _ = ∫ z : ℝ × Phase, Real.log ((S.density (z.1,TorusFlight.flight z.1 z.2)+δ*maxwellian z.2.2)/maxwellian z.2.2)*
        S.collision (z.1,TorusFlight.flight z.1 z.2) ∂(volume.restrict (Icc 0 t)).prod volume :=
      (integral_prod_symm _ halong).symm
    _ = _ := TorusFlight.integral_along hi

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite cutoff solutions satisfy a cutoff-independent entropy bound -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.endpoint_entropy_tendsto (S : BoundedCutoffSolution N T f₀) (t : ℝ) :
    Tendsto (fun δ : ℝ => ∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))
      (𝓝[>] 0) (𝓝 (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p)))) := by
  obtain ⟨B,hB⟩ := S.bounded
  simp only [Measure.volume_eq_prod]
  exact regularizedEntropy_integral_tendsto
    (S.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => S.nonnegative (t,p)) (fun p => hB (t,p)) (fun p => S.support (t,p))

theorem BoundedCutoffSolution.entropy_inequality (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p))) ≤
      ∫ p, scalarRelativeEntropy (maxwellian p.2) (f₀ p) := by
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have h0 := S.endpoint_entropy_tendsto 0
  simp only [S.initial hT] at h0
  have hL := (S.endpoint_entropy_tendsto t).sub h0
  have hR := (entropy_error_tendsto
    ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N B).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
  have hle : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
        (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) ≤
      entropyErrorCoefficient ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N*
        δ*(|Real.log δ|+logRegularizationConstant N B) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    rw [S.integrated_entropy_balance hN hT ht hδ.1 hδ.2.le]
    exact S.entropy_production_bound hN hB hSb hδ.1 hδ.2.le t
  have h := le_of_tendsto_of_tendsto hL hR hle
  linarith

theorem BoundedCutoffSolution.relativeEntropy_le (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    relativeEntropy (fun p => S.density (t,p)) ≤ relativeEntropy f₀ := by
  have h := S.entropy_inequality hN hT ht
  simpa only [relativeEntropy,scalarRelativeEntropy_eq (maxwellian_pos _)] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The hard-sphere kernel satisfies Levermore–Masmoudi (4.4) -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BoltzmannNonuniqueness

def compactKernelMass (K : Set Velocity) (v : Velocity) : ℝ :=
  ∫ w in K, ∫ ω : Sphere, collisionKernel v w ω ∂sphereArea

theorem compactKernelMass_eq (K : Set Velocity) (v : Velocity) :
    compactKernelMass K v = 2*Real.pi*(∫ w in K, ‖v-w‖) := by
  simp only [compactKernelMass,integral_collisionKernel_sphereArea,integral_const_mul]

theorem compactKernelMass_nonneg (K : Set Velocity) (v : Velocity) :
    0 ≤ compactKernelMass K v := by
  rw [compactKernelMass_eq]
  exact mul_nonneg (by positivity) (integral_nonneg (fun _ => norm_nonneg _))

theorem compactKernelMass_le {K : Set Velocity} (hK : IsCompact K)
    {R : ℝ} (hR : ∀ w ∈ K, ‖w‖ ≤ R) (v : Velocity) :
    compactKernelMass K v ≤ 2*Real.pi*volume.real K*(‖v‖+R) := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using (show volume K < ⊤ from hK.measure_lt_top)⟩
  have hi : IntegrableOn (fun w => ‖v-w‖) K :=
    (by fun_prop : Continuous (fun w : Velocity => ‖v-w‖)).continuousOn.integrableOn_compact hK
  have hb : (∫ w in K, ‖v-w‖) ≤ (‖v‖+R)*volume.real K := by
    calc
      _ ≤ ∫ _ in K, (‖v‖+R) := by
        apply integral_mono_ae hi (integrable_const _)
        filter_upwards [ae_restrict_mem hK.measurableSet] with w hw
        exact (norm_sub_le v w).trans (add_le_add le_rfl (hR w hw))
      _ = _ := by rw [integral_const]; simp only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ]; ring
  rw [compactKernelMass_eq]
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*Real.pi by positivity)
  nlinarith

theorem linear_over_quadratic_bound {x R : ℝ} (hx : 0 ≤ x) (hR : 0 ≤ R) :
    (x+R)/(1+x^2) ≤ 2*(1+R)/(1+x) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  calc
    (x+R)*(1+x) ≤ ((1+R)*(1+x))*(1+x) := by
      gcongr
      nlinarith [mul_nonneg hx hR]
    _ = (1+R)*(1+x)^2 := by ring
    _ ≤ (1+R)*(2*(1+x^2)) := by
      gcongr
      nlinarith [sq_nonneg (x-1)]
    _ = _ := by ring

theorem hardSphere_kernel_condition (K : Set Velocity) (hK : IsCompact K) :
    Tendsto (fun v => compactKernelMass K v/(1+‖v‖^2)) (cocompact Velocity) (𝓝 0) := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  let C := 2*Real.pi*volume.real K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb v : compactKernelMass K v/(1+‖v‖^2) ≤ C*(2*(1+max R 0)/(1+‖v‖)) := by
    calc
      _ ≤ C*(‖v‖+max R 0)/(1+‖v‖^2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact compactKernelMass_le hK (fun w hw => (hR w hw).trans (le_max_left _ _)) v
      _ = C*((‖v‖+max R 0)/(1+‖v‖^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (linear_over_quadratic_bound (norm_nonneg _) (le_max_right _ _)) hC
  have ht : Tendsto (fun v : Velocity => C*(2*(1+max R 0)/(1+‖v‖)))
      (cocompact Velocity) (𝓝 0) := by
    have hnorm : Tendsto (fun v : Velocity => ‖v‖) (cocompact Velocity) atTop :=
      tendsto_norm_cocompact_atTop
    have hn : Tendsto (fun v : Velocity => 2*(1+max R 0)/(1+‖v‖))
        (cocompact Velocity) (𝓝 0) := tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 hnorm)
    simpa using hn.const_mul C
  exact squeeze_zero (fun v => div_nonneg (compactKernelMass_nonneg K v) (by positivity)) hb ht

end BoltzmannNonuniqueness

end

end

section

/-! # Retained dissipation of the actual finite periodic solutions -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.kineticProfile (S : BoundedCutoffSolution N T f₀) :
    (ℝ × Position) × Velocity → ℝ := fun p => S.density (p.1.1,(p.1.2,p.2))

theorem BoundedCutoffSolution.kineticProfile_measurable (S : BoundedCutoffSolution N T f₀) :
    Measurable S.kineticProfile :=
  S.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))

theorem BoundedCutoffSolution.kinetic_entropy_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t δ : ℝ} (ht : t ∈ Icc 0 T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (∫ p, Real.log (gaussianShift δ S.kineticProfile p/maxwellian p.2)*
      collisionOperator N S.kineticProfile p
      ∂((volume.restrict (Icc 0 t)).prod (volume : Measure Position)).prod volume) =
    (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
      (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)) := by
  have he := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 t))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding
    (fun z : ℝ × Phase => Real.log ((S.density z+δ*maxwellian z.2.2)/maxwellian z.2.2)*S.collision z)
  have hi := (S.integrated_entropy_balance hN hT ht hδ hδ1).symm
  rw [← he] at hi
  have hc (p : (ℝ × Position) × Velocity) : collisionOperator N S.kineticProfile p =
      S.collision (p.1.1,(p.1.2,p.2)) := S.kinetic_collision p
  simp only [hc,kineticProfile,gaussianShift]
  convert hi using 1
  congr 1

theorem BoundedCutoffSolution.extended_dissipation_le (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    extendedDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position)) N S.kineticProfile ≤
      ENNReal.ofReal ((∫ p, scalarRelativeEntropy (maxwellian p.2) (f₀ p))-
        (∫ p, scalarRelativeEntropy (maxwellian p.2) (S.density (t,p)))) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 t)).prod volume
  obtain ⟨B,hSb⟩ := S.bounded
  have hB : 0 ≤ B := (S.nonnegative (0,0)).trans (hSb (0,0))
  have hf : ∀ p, 0 ≤ S.kineticProfile p := fun p => S.nonnegative _
  have h0 := S.endpoint_entropy_tendsto 0
  simp only [S.initial hT] at h0
  have hlim := ((entropy_error_tendsto μ N B).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)).sub ((S.endpoint_entropy_tendsto t).sub h0)
  have hu : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      extendedDissipation μ N (gaussianShift δ S.kineticProfile) ≤
      ENNReal.ofReal (entropyErrorCoefficient μ N*δ*(|Real.log δ|+logRegularizationConstant N B)-
        ((∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (S.density (t,p)))-
          (∫ p, regularizedEntropy (maxwellian p.2) (maxwellian p.2) δ (f₀ p)))) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    have hp := gaussian_entropy_dissipation_bound (μ := μ) hN hB hδ.1 hδ.2.le
      S.kineticProfile_measurable hf (fun p => hSb _)
    rw [S.kinetic_entropy_balance hN hT ht hδ.1 hδ.2.le] at hp
    have hlog := fun (p : (ℝ × Position) × Velocity) (hp : ‖p.2‖ ≤ N) =>
      log_regularization_bound hN.le hB hδ.1 hδ.2.le (hf p) (hSb _) p.2 hp
    have hpi := (positiveProduction_identity (μ := μ) hN
      (gaussianShift_measurable δ S.kineticProfile_measurable) (gaussianShift_pos hδ.1 hf) hlog).1
    rw [← ofReal_integral_positiveProduction hN.le _ (gaussianShift_pos hδ.1 hf) hpi]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hupper := liminf_le_liminf hu
  rw [(ENNReal.tendsto_ofReal hlim).liminf_eq] at hupper
  have hlower := extendedDissipation_gaussian_le_liminf μ hN S.kineticProfile_measurable hf
  exact (hlower.trans hupper).trans_eq (by congr 1; ring)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual cutoff collision source vanishes against each local mass test -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem BoundedCutoffSolution.mass_source_zero {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) (R : ℝ) (φ : MassTest) :
    Integrable (fun z : ℝ × Phase => S.collision z*φ.toFun z.1 z.2.1)
      ((volume.restrict (Icc 0 R)).prod (volume : Measure Phase)) ∧
    (∫ z, S.collision z*φ.toFun z.1 z.2.1
      ∂(volume.restrict (Icc 0 R)).prod (volume : Measure Phase)) = 0 := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 R)).prod volume
  let ψ : (ℝ × Position) × Velocity → ℝ :=
    fun p => if p.1.1 ∈ Icc 0 R then φ.toFun p.1.1 p.1.2 else 0
  have hψm : Measurable ψ := ((φ.measurable_toFun.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).ite
    (measurableSet_Icc.preimage measurable_fst.fst) measurable_const)
  obtain ⟨C,hC,hb⟩ := φ.bounded_on_time R
  have hψb p (_hp : ‖p.2‖ ≤ N) : |ψ p| ≤ C := by
    dsimp only [ψ]
    split_ifs with ht
    · exact (hb p.1.1 ht (p.1.2,p.2)).1
    · simpa only [abs_zero] using hC
  have hp := regularized_test_marginals (μ := μ) hN S.kineticProfile_measurable
    (fun p => S.nonnegative _) hψm hψb
  have he := regularized_test_invariant (μ := μ) hN S.kineticProfile_measurable
    (fun p => S.nonnegative _) hψm hψb (by intro z; simp [collisionJump,ψ])
  have hi : Integrable (fun p => ψ p*(gain N S.kineticProfile p-loss N S.kineticProfile p))
      (μ.prod volume) := by
    convert hp.1.sub hp.2.1 using 1
    ext p
    exact mul_sub _ _ _
  have hz : (∫ p, ψ p*(gain N S.kineticProfile p-loss N S.kineticProfile p) ∂μ.prod volume) = 0 := by
    simp_rw [mul_sub]
    rw [integral_sub hp.1 hp.2.1,he,sub_self]
  have hgroup := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 R))).symm
  have hie := hgroup.integrable_comp_of_integrable hi
  have heq : (fun z : ℝ × Phase => ψ ((MeasurableEquiv.prodAssoc : ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase).symm z)*
      (gain N S.kineticProfile ((MeasurableEquiv.prodAssoc : ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase).symm z)-loss N S.kineticProfile ((MeasurableEquiv.prodAssoc : ((ℝ × Position) × Velocity) ≃ᵐ ℝ × Phase).symm z))) =ᵐ[
        (volume.restrict (Icc 0 R)).prod (volume : Measure Phase)]
      (fun z => S.collision z*φ.toFun z.1 z.2.1) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z ht
    change (if z.1 ∈ Icc 0 R then φ.toFun z.1 z.2.1 else 0)*
      (gain N S.kineticProfile ((z.1,z.2.1),z.2.2)-
       loss N S.kineticProfile ((z.1,z.2.1),z.2.2)) = _
    rw [ite_eq_left_iff.mpr (fun h => (h ht).elim), S.collision_eq]
    exact mul_comm _ _
  refine ⟨hie.congr heq,?_⟩
  rw [← integral_congr_ae heq]
  exact (hgroup.integral_comp MeasurableEquiv.prodAssoc.symm.measurableEmbedding
    (fun p => ψ p*(gain N S.kineticProfile p-loss N S.kineticProfile p))).trans hz

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One entropy and moment budget for all finite regularized approximants -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def initialEntropyBudget (f : Density) : ℝ :=
  initialEntropyCoefficient*(∫ p, entropyMoment f p)+(∫ p : Phase, maxwellian p.2)

def approximationEntropyBudget (f : Density) : ℝ :=
  (1+4*entropyMomentCoefficient)*initialEntropyBudget f+
    4*entropyMomentCoefficient*(∫ p : Phase, entropyGaussian p.2)+(∫ p : Phase, maxwellian p.2)

theorem BoundedCutoffSolution.uniform_entropyMoment {N T : ℝ} {f : Density}
    (S : BoundedCutoffSolution N T (initialApproximation N f))
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ approximationEntropyBudget f := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hE := entropyMoment_integral_control (S.finiteEntropy hN0.le t)
  have hR := (S.relativeEntropy_le hN0 hT ht).trans
    (initialApproximation_relativeEntropy_le hN hfm hf hi)
  have hC : 0 ≤ 1+4*entropyMomentCoefficient := by
    have := entropyMomentCoefficient_nonneg
    positivity
  exact hE.trans (by
    change (1+4*entropyMomentCoefficient)*relativeEntropy (fun p => S.density (t,p))+_+_ ≤
      (1+4*entropyMomentCoefficient)*initialEntropyBudget f+_+_
    gcongr
    exact hR)

theorem exists_uniform_entropy_approximation {N T : ℝ} (hN : 1 ≤ N) (hT : 0 ≤ T)
    {f : Density} (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ S : BoundedCutoffSolution N T (initialApproximation N f),
      ∀ t ∈ Icc 0 T, (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ approximationEntropyBudget f := by
  obtain ⟨S⟩ := exists_initial_approximation_solution (lt_of_lt_of_le zero_lt_one hN) hT hfm
  exact ⟨S,fun _ ht => S.uniform_entropyMoment hN hT hfm hf hi ht⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual cutoff solution sequence with growing horizons and uniform entropy -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem clippedTime_fixed {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    PositiveIntegral.time T (PositiveIntegral.time T t) = PositiveIntegral.time T t := by
  have ht := PositiveIntegral.time_bounds hT t
  change max 0 (min T (PositiveIntegral.time T t)) = PositiveIntegral.time T t
  rw [min_eq_right ht.2,max_eq_right ht.1]

theorem BoundedCutoffSolution.density_clipped {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hT : 0 ≤ T) (t : ℝ) (p : Phase) :
    S.density (t,p) = S.density (PositiveIntegral.time T t,p) := by
  rw [S.mild (t,p),S.mild (PositiveIntegral.time T t,p)]
  simp only [PositiveIntegral.value,clippedTime_fixed hT]

theorem BoundedCutoffSolution.uniform_entropyMoment_all_times {N T : ℝ} {f : Density}
    (S : BoundedCutoffSolution N T (initialApproximation N f))
    (hN : 1 ≤ N) (hT : 0 ≤ T) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p)
    (hi : Integrable (entropyMoment f)) (t : ℝ) :
    (∫ p, entropyMoment (fun p => S.density (t,p)) p) ≤ approximationEntropyBudget f := by
  have he : (fun p => S.density (t,p)) = (fun p => S.density (PositiveIntegral.time T t,p)) :=
    funext (S.density_clipped hT t)
  rw [he]
  exact S.uniform_entropyMoment hN hT hfm hf hi (PositiveIntegral.time_bounds hT t)

def approximatingSolution (f : Density) (hfm : Measurable f) (n : ℕ) :
    BoundedCutoffSolution ((n:ℝ)+1) ((n:ℝ)+1) (initialApproximation ((n:ℝ)+1) f) :=
  Classical.choice (exists_initial_approximation_solution (by positivity) (by positivity) hfm)

theorem approximatingSolution_entropy (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ) (t : ℝ) :
    (∫ p, entropyMoment (fun p => (approximatingSolution f hfm n).density (t,p)) p) ≤
      approximationEntropyBudget f := by
  exact (approximatingSolution f hfm n).uniform_entropyMoment_all_times
    (by have := Nat.cast_nonneg (α := ℝ) n; linarith) (by positivity) hfm hf hi t

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong L1 continuity of the actual bounded periodic approximants -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.initial_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 ≤ N) (hT : 0 ≤ T) : Integrable f₀ := by
  have h := S.weighted_density_integrable hN (fun _ => 1) measurable_const
    (fun _ _ => by norm_num : ∀ v : Velocity, ‖v‖ ≤ N → |(1:ℝ)| ≤ 1) 0
  simpa only [one_mul,S.initial hT] using h

theorem BoundedCutoffSolution.characteristicSource_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) : Integrable S.characteristicSource
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have h := S.weighted_characteristic_integrable hN (fun _ => 1) measurable_const
    (fun _ _ => by norm_num : ∀ v : Velocity, ‖v‖ ≤ N → |(1:ℝ)| ≤ 1)
  simpa only [one_mul] using h

theorem BoundedCutoffSolution.strong_continuity (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p => S.density (s,p)-S.density (t,p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have h := TorusFlight.eulerianProfile_L1_continuous hT (S.initial_integrable hN.le hT)
    S.characteristicSource_measurable (S.characteristicSource_integrable hN) ht
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [S.eulerianProfile_eq hN hs,S.eulerianProfile_eq hN ht]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable renormalized fields of the actual periodic solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

def BoundedCutoffSolution.renormalizedDensity (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  maxwellian z.2.2*β.toFun (S.density z/maxwellian z.2.2)

def BoundedCutoffSolution.renormalizedSource (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (z : ℝ × Phase) : ℝ :=
  derivWithin β.toFun (Ici 0) (S.density z/maxwellian z.2.2)*S.collision z

def BoundedCutoffSolution.renormalizedIntegrand (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) (φ : KineticTest) (z : ℝ × Phase) : ℝ :=
  S.renormalizedDensity β z*φ.transportDerivative z.1 z.2+
    S.renormalizedSource β z*φ.toFun z.1 z.2.1 z.2.2

theorem BoundedCutoffSolution.spacetime_density_integrable (S : BoundedCutoffSolution N T f₀) :
    Integrable S.density ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  obtain ⟨B,hB⟩ := S.bounded
  have hm : Measurable (fun p : (ℝ × Position) × Velocity => S.density (p.1.1,(p.1.2,p.2))) :=
    S.measurable.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hi := bounded_velocity_integrable
    (μ := (volume.restrict (Icc 0 T)).prod (volume : Measure Position))
    (N := N) hm
    (fun p => (abs_of_nonneg (S.nonnegative _)).trans_le (hB _))
    (fun p hp => S.support _ hp)
  have h := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable hi
  change Integrable S.density ((volume.restrict (Icc 0 T)).prod
    ((volume : Measure Position).prod (volume : Measure Velocity))) at h
  simpa only [Measure.volume_eq_prod] using h

theorem BoundedCutoffSolution.renormalizedDensity_measurable (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) : Measurable (S.renormalizedDensity β) :=
  β.weighted_measurable S.measurable (by unfold maxwellian; fun_prop)
    S.nonnegative (fun z => maxwellian_pos z.2.2)

theorem BoundedCutoffSolution.renormalizedSource_measurable (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) : Measurable (S.renormalizedSource β) :=
  (β.measurable_derivative_comp (S.measurable.div (by unfold maxwellian; fun_prop))
    (fun z => div_nonneg (S.nonnegative z) (maxwellian_pos z.2.2).le)).mul S.collision_measurable

theorem BoundedCutoffSolution.renormalizedDensity_integrable (S : BoundedCutoffSolution N T f₀)
    (β : Renormalization) :
    Integrable (S.renormalizedDensity β) ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) :=
  β.weighted_integrable S.measurable (by unfold maxwellian; fun_prop)
    S.nonnegative (fun z => maxwellian_pos z.2.2) S.spacetime_density_integrable

theorem BoundedCutoffSolution.renormalizedSource_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (β : Renormalization) :
    Integrable (S.renormalizedSource β) ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  have hi := S.weighted_collision_integrable hN (fun _ => 1) measurable_const
    (fun _ _ => by norm_num : ∀ v : Velocity, ‖v‖ ≤ N → |(1:ℝ)| ≤ 1)
  simp only [one_mul] at hi
  exact β.derivative_mul_integrable (S.measurable.div (by unfold maxwellian; fun_prop))
    (fun z => div_nonneg (S.nonnegative z) (maxwellian_pos z.2.2).le) hi

theorem BoundedCutoffSolution.renormalizedIntegrand_integrable (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (β : Renormalization) (φ : KineticTest) :
    Integrable (S.renormalizedIntegrand β φ) ((volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) := by
  obtain ⟨C,_,hC⟩ := φ.bounded_on_time T
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hb₁ : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume,
      ‖φ.transportDerivative z.1 z.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hC z.1 hz z.2).2
  have hb₂ : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume,
      ‖φ.toFun z.1 z.2.1 z.2.2‖ ≤ C := by
    filter_upwards [ht] with z hz
    simpa only [Real.norm_eq_abs] using (hC z.1 hz z.2).1
  exact ((S.renormalizedDensity_integrable β).mul_bdd
    φ.measurable_transportDerivative.aestronglyMeasurable hb₁).add
      ((S.renormalizedSource_integrable hN β).mul_bdd φ.measurable_toFun.aestronglyMeasurable hb₂)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The exact weak renormalized equation of the actual cutoff solution -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.renormalized_balance (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest) :
    (∫ z, S.renormalizedIntegrand β φ z
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) =
      (∫ p : Phase, maxwellian p.2*β.toFun (S.density (T,p)/maxwellian p.2)*φ.toFun T p.1 p.2)-
      (∫ p : Phase, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let B : Phase → ℝ := fun p => maxwellian p.2*β.toFun (S.density (T,p)/maxwellian p.2)*φ.toFun T p.1 p.2
  let B₀ : Phase → ℝ := fun p => maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2
  have hIi := S.renormalizedIntegrand_integrable hN β φ
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hf (t : ℝ) : Integrable (fun p => S.density (t,p)) := by
    simpa only [one_mul] using S.weighted_density_integrable hN.le (fun _ => 1)
      measurable_const (fun _ _ => by norm_num : ∀ v : Velocity, ‖v‖ ≤ N → |(1:ℝ)| ≤ 1) t
  have hBi : Integrable B := φ.weighted_slice_integrable β ⟨hT,le_rfl⟩
    (S.measurable.comp (measurable_const.prodMk measurable_id)) (fun p => S.nonnegative (T,p)) (hf T)
  have hf₀m : Measurable f₀ := by
    have hm : Measurable (fun p : Phase => S.density (0,p)) :=
      S.measurable.comp (measurable_const.prodMk measurable_id)
    simpa only [S.initial hT] using hm
  have hf₀n (p : Phase) : 0 ≤ f₀ p := by simpa only [S.initial hT] using S.nonnegative (0,p)
  have hB₀i : Integrable B₀ := φ.weighted_slice_integrable β ⟨le_rfl,hT⟩ hf₀m hf₀n
    (S.initial_integrable hN.le hT)
  have hp (p : Phase) : (∫ t, TorusFlight.along (S.renormalizedIntegrand β φ) (t,p) ∂μ) =
      B (TorusFlight.flight T p)-B₀ p := by
    have h := S.renormalized_tested_path hN ⟨hT,le_rfl⟩ β φ p
    rw [intervalIntegral.integral_of_le hT,← integral_Icc_eq_integral_Ioc] at h
    change (∫ r, S.renormalizedDensity β (r,TorusFlight.flight r p)*
      φ.transportDerivative r (TorusFlight.flight r p)+
      S.renormalizedSource β (r,TorusFlight.flight r p)*φ.toFun r (TorusFlight.flight r p).1 p.2 ∂μ) = _
    rw [show (fun r => S.renormalizedDensity β (r,TorusFlight.flight r p)*
        φ.transportDerivative r (TorusFlight.flight r p)+
        S.renormalizedSource β (r,TorusFlight.flight r p)*φ.toFun r (TorusFlight.flight r p).1 p.2) =
      (fun r => S.renormalizedSource β (r,TorusFlight.flight r p)*φ.toFun r (TorusFlight.flight r p).1 p.2+
        S.renormalizedDensity β (r,TorusFlight.flight r p)*φ.transportDerivative r (TorusFlight.flight r p))
      from funext (fun _ => add_comm _ _)]
    exact h
  calc
    _ = ∫ z, TorusFlight.along (S.renormalizedIntegrand β φ) z ∂μ.prod volume :=
      (TorusFlight.integral_along hIi).symm
    _ = ∫ p : Phase, ∫ t, TorusFlight.along (S.renormalizedIntegrand β φ) (t,p) ∂μ :=
      integral_prod_symm _ hAi
    _ = ∫ p : Phase, B (TorusFlight.flight T p)-B₀ p := integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = (∫ p : Phase, B (TorusFlight.flight T p))-(∫ p : Phase, B₀ p) :=
      integral_sub ((TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hBi) hB₀i
    _ = _ := by rw [TorusFlight.integral_flight]

theorem BoundedCutoffSolution.renormalized_equation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest)
    (hφ : ∀ x v, φ.toFun T x v = 0) :
    (∫ z, S.renormalizedIntegrand β φ z
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
      (∫ p : Phase, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  rw [S.renormalized_balance hN hT β φ]
  simp only [hφ,mul_zero,integral_zero,zero_sub,neg_add_cancel]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Conserved mass, energy, and momentum coordinates of each actual approximation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness
variable {N T : ℝ} {f₀ : Density}

theorem BoundedCutoffSolution.mass_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, S.density (t,p)) = ∫ p, f₀ p := by
  simpa only [one_mul] using S.moment_conservation hN (ht.1.trans ht.2) (fun _ => (1:ℝ))
    measurable_const (C := 1) (fun _ _ => by norm_num) (collisionJump_mass (fun _ => 1)) ht

theorem BoundedCutoffSolution.energy_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T) : energy (fun p => S.density (t,p)) = energy f₀ := by
  apply S.moment_conservation hN (ht.1.trans ht.2) (fun v => ‖v‖^2)
    (measurable_id.norm.pow_const 2) (C := N^2) _ collisionJump_energy ht
  intro v hv
  rw [abs_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg v) hN.le).mpr hv

theorem BoundedCutoffSolution.momentum_coordinate_conservation (S : BoundedCutoffSolution N T f₀)
    (hN : 0 < N) (i : Fin 3) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, (p.2 i)*S.density (t,p)) = ∫ p : Phase, (p.2 i)*f₀ p := by
  apply S.moment_conservation hN (ht.1.trans ht.2) (fun v => v i)
    (by fun_prop) (C := N) _ (collisionJump_momentum i) ht
  intro v hv
  have h : |v i| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v i
  exact h.trans hv

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local mass tests along the actual cutoff characteristics -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.mass_tested_path {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 T)
    (φ : MassTest) (p : Phase) :
    (∫ r in 0..t, S.density (r,TorusFlight.flight r p)*φ.transportDerivative r (TorusFlight.flight r p)+
      S.collision (r,TorusFlight.flight r p)*φ.toFun r (TorusFlight.flight r p).1) =
      S.density (t,TorusFlight.flight t p)*φ.toFun t (TorusFlight.flight t p).1-f₀ p*φ.toFun 0 p.1 := by
  have hd : (fun r => φ.transportDerivative r (TorusFlight.flight r p)) =
      deriv (fun r => φ.toFun r (TorusFlight.flight r p).1) :=
    funext (fun r => (φ.hasDerivAt_along p r).deriv.symm)
  have hD : Continuous (fun r => φ.transportDerivative r (TorusFlight.flight r p)) := by
    rw [hd]
    exact (φ.contDiff_along p).continuous_deriv (by simp)
  have h := S.tested_path hN ht p
    (fun r => φ.toFun r (TorusFlight.flight r p).1)
    (fun r => φ.transportDerivative r (TorusFlight.flight r p))
    (φ.contDiff_along p).continuous.continuousOn hD.continuousOn
    (fun r _ => φ.hasDerivAt_along p r)
  simpa only [BoundedCutoffSolution.collision,mul_comm,TorusFlight.flight_zero] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
