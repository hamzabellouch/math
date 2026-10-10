import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicCutoffGeometry
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.RateDissipationMonotone
import OAI.MathematicalPhysics.Boltzmann.Branching.RightAverageBound
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionSources
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantPowers
import OAI.MathematicalPhysics.Boltzmann.Collision.ScalarEntropyJointTrace
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyUniformIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicLinearApproximation
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicWeakCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalDissipationBridge
import OAI.MathematicalPhysics.Boltzmann.Compactness.PhysicalLinearContinuous
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakLinearMomentLimit
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # The actual global density equals its nonlinear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_eq_density_local
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 R))),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  have hU := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    (G.linear_profile_approximation_L1 hf hi hT hR)
  have hF := tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top
    (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ∞)
    ((G.characteristic_density_strong hf hi hT hR).comp (tendsto_add_atTop_nat (Nat.ceil T)))
  have he := tendstoInMeasure_ae_unique hU hF
  filter_upwards [he,Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem measurableSet_Icc)] with z hz ht
  have hpos : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile z :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht.1 z.2
  rw [max_eq_right hpos] at hz
  exact hz

theorem GlobalCollisionLimit.linear_profile_eq_density
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalLinearProfile f G.weakLimit.kineticProfile z =
        G.weakLimit.density (z.1,TorusFlight.flight z.1 z.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hall : ∀ᵐ z ∂(μ.prod (volume : Measure Position)).prod (volume : Measure Velocity),
      physicalLinearProfile f G.weakLimit.kineticProfile (z.1.1,(z.1.2,z.2)) =
        G.weakLimit.density (z.1.1,TorusFlight.flight z.1.1 (z.1.2,z.2)) := by
    apply ae_prod_of_velocity_windows
    intro n
    exact (measurePreserving_prodAssoc μ (volume : Measure Position)
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 (n:ℝ)))).quasiMeasurePreserving.ae
      (G.linear_profile_eq_density_local hf hi hT (Nat.cast_nonneg n))
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure Velocity)).symm.quasiMeasurePreserving.ae hall

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The original entropy budget holds almost everywhere along the linear profile -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_entropy_bound_ae_on_window
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  filter_upwards [Measure.ae_ae_of_ae_prod (G.linear_profile_eq_density hf hi hT),
    ae_restrict_of_ae (G.weakLimit.finiteEntropy_ae_volume hf hi)] with t he hdata
  calc
    _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (G.weakLimit.density (t,TorusFlight.flight t p))) :=
      lintegral_congr_ae (he.mono (fun p hp => by rw [hp]))
    _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (G.weakLimit.density (t,p))) :=
      TorusFlight.scalar_entropy_lintegral_comp
        (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id)) t
    _ = ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p))) :=
      (relativeEntropy_eq_lintegral hdata.1).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hdata.2

theorem GlobalCollisionLimit.linear_entropy_bound_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  have hh n := G.linear_entropy_bound_ae_on_window hf hi (Nat.cast_nonneg n)
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The entropy bound and finite entropy at every characteristic time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_entropy_bound
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence (G.linear_entropy_bound_ae hf hi) t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  have hc := G.linear_profile_slice_tendsto hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst
  exact scalarEntropy_trace_bound
    (U := physicalLinearProfile f G.weakLimit.kineticProfile)
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
    hc (fun n => (hs n).2.2 (ht.trans (hs n).1.le))

theorem GlobalCollisionLimit.linear_finiteEntropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    FiniteEntropyDatum (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) := by
  have hum : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id)
  have hun p : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile (t,p) :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) ht p
  have hmm : Measurable (fun p : Phase => maxwellian p.2) := by unfold maxwellian; fun_prop
  have hH : Integrable (fun p : Phase => scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))) := by
    refine ⟨?_,(hasFiniteIntegral_iff_ofReal ?_).mpr
      ((G.linear_entropy_bound hf hi ht).trans_lt ENNReal.ofReal_lt_top)⟩
    · exact (((hum.mul hum.log).sub (hum.mul (measurable_const.add hmm.log))).add hmm).aestronglyMeasurable
    · exact ae_of_all _ (fun p => scalarRelativeEntropy_nonneg (maxwellian_pos p.2) (hun p))
  exact finiteEntropy_of_relativeEntropy_integrable hum hun hH

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A common entropy-moment budget for every characteristic time -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalEntropyBudget (f : Density) : ℝ :=
  (1+4*entropyMomentCoefficient)*relativeEntropy f+
    4*entropyMomentCoefficient*(∫ p : Phase, entropyGaussian p.2)+
      (∫ p : Phase, maxwellian p.2)

theorem GlobalCollisionLimit.linear_relativeEntropy_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    relativeEntropy (fun p => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) ≤
      relativeEntropy f := by
  have hb := G.linear_entropy_bound hf hi ht
  rw [← relativeEntropy_eq_lintegral (G.linear_finiteEntropy hf hi ht)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (relativeEntropy_nonneg
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩))).mp hb

theorem GlobalCollisionLimit.linear_entropyMoment_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, entropyMoment (fun p => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) p) ≤
      physicalEntropyBudget f := by
  have hb := entropyMoment_integral_control (G.linear_finiteEntropy hf hi ht)
  apply hb.trans
  dsimp only [physicalEntropyBudget]
  apply add_le_add _ le_rfl
  apply add_le_add _ le_rfl
  apply mul_le_mul_of_nonneg_left (G.linear_relativeEntropy_le hf hi ht)
  have := entropyMomentCoefficient_nonneg
  positivity

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The joint entropy and full earlier dissipation bound at every characteristic time -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.linear_joint_entropy_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
        (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))))+
      rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  have hh n := Measure.ae_ae_of_ae_prod (G.linear_profile_eq_density hf hi (Nat.cast_nonneg n))
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh,G.sharp_joint_entropy_dissipation hf hi,
    G.weakLimit.finiteEntropy_ae_volume hf hi] with t he hbound hdata
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  have hslice := he n ⟨ht0,hn⟩
  have hH : (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p)))) =
      ENNReal.ofReal (relativeEntropy (fun p => G.weakLimit.density (t,p))) := by
    calc
      _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
          (G.weakLimit.density (t,TorusFlight.flight t p))) :=
        lintegral_congr_ae (hslice.mono (fun p hp => by rw [hp]))
      _ = ∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
          (G.weakLimit.density (t,p))) :=
        TorusFlight.scalar_entropy_lintegral_comp
          (G.weakLimit.measurable.comp (measurable_const.prodMk measurable_id)) t
      _ = _ := (relativeEntropy_eq_lintegral hdata.1).symm
  rw [hH]
  exact hbound ht0

theorem GlobalCollisionLimit.linear_joint_entropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫⁻ p : Phase, ENNReal.ofReal (scalarRelativeEntropy (maxwellian p.2)
      (physicalLinearProfile f G.weakLimit.kineticProfile (t,p))))+
      rateDissipation ((volume.restrict (Icc 0 t)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ ENNReal.ofReal (relativeEntropy f) := by
  obtain ⟨s,hs,hst⟩ := exists_right_good_sequence (G.linear_joint_entropy_ae hf hi) t
  have hsm n : s n ∈ Icc 0 (t+1) := by
    have hδ : 1/((n:ℝ)+1) ≤ 1 := (div_le_iff₀ (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
    exact ⟨ht.trans (hs n).1.le,(hs n).2.1.le.trans (add_le_add le_rfl hδ)⟩
  apply scalarEntropy_joint_trace_bound
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable)
    (G.linear_profile_slice_tendsto hf hi (show 0 ≤ t+1 by linarith)
      (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩) hsm hst)
  intro n
  have hD := rateDissipation_mono_measure
    (Measure.prod_mono (Measure.restrict_mono_set (volume : Measure ℝ)
      (show Icc (0:ℝ) t ⊆ Icc 0 (s n) from Icc_subset_Icc_right (hs n).1.le))
      (le_refl (volume : Measure Position))) G.weakLimit.kineticProfile
  apply le_trans (add_le_add le_rfl hD)
  exact (hs n).2.2 (hsm n).1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong L1 time continuity of the nonlinear characteristic profile -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.linear_profile_strong_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => eLpNorm (fun p : Phase =>
      physicalLinearProfile f G.weakLimit.kineticProfile (s n,p)-
        physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 1 volume) atTop (𝓝 0) := by
  let U (r : ℝ) (p : Phase) := physicalLinearProfile f G.weakLimit.kineticProfile (r,p)
  have hum n : Measurable (U (s n)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id)
  have hun n p : 0 ≤ U (s n) p :=
    physicalLinearProfile_nonneg hf (fun _ => G.weakLimit.nonnegative _) (hs n).1 p
  have hui n : Integrable (entropyGauge (U (s n))) := (G.linear_finiteEntropy hf hi (hs n).1).2.2
  have hub n : (∫ p, entropyGauge (U (s n)) p) ≤ physicalEntropyBudget f :=
    G.linear_entropyMoment_le hf hi (hs n).1
  have hUI := uniformIntegrable_of_entropyGauge (μ := (volume : Measure Position)) hum hun hui hub
  have hUT := unifTight_of_entropyGauge (μ := (volume : Measure Position)) hum hun hui hub
  have hmem := memLp_one_iff_integrable.mpr (G.linear_finiteEntropy hf hi ht.1).integrable
  exact tendsto_Lp_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (hum n).aestronglyMeasurable) hmem hUI.1 hUT
    (G.linear_profile_slice_tendsto hf hi hT ht hs hst)

theorem GlobalCollisionLimit.linear_profile_strong_continuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p : Phase =>
      physicalLinearProfile f G.weakLimit.kineticProfile (s,p)-
        physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro s hs
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_mem_of_tendsto_nhdsWithin hs)
  have hst := (tendsto_nhds_of_tendsto_nhdsWithin hs).comp (tendsto_add_atTop_nat N)
  have hh := G.linear_profile_strong_seq hf hi hT ht
    (fun n => hN (n+N) (Nat.le_add_left N n)) hst
  exact (tendsto_add_atTop_iff_nat N).mp hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The measurable nonnegative evolution defined by the characteristic profile -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

def physicalEvolution (f : Density) (F : (ℝ × Position) × Velocity → ℝ) : Evolution :=
  fun t p => max 0 (physicalLinearProfile f F (t,TorusFlight.flight (-t) p))

theorem physicalEvolution_measurable {f : Density} (hfm : Measurable f)
    {F : (ℝ × Position) × Velocity → ℝ} (hFm : Measurable F) :
    Measurable (fun z : ℝ × Phase => physicalEvolution f F z.1 z.2) := by
  apply measurable_const.max
  exact (physicalLinearProfile_measurable hfm hFm).comp
    (measurable_fst.prodMk (TorusFlight.measurable_flight.comp
      (measurable_fst.neg.prodMk measurable_snd)))

theorem physicalEvolution_nonneg (f : Density) (F : (ℝ × Position) × Velocity → ℝ)
    (t : ℝ) (p : Phase) : 0 ≤ physicalEvolution f F t p := le_max_left _ _

theorem physicalEvolution_initial {f : Density} (hf : ∀ p, 0 ≤ f p)
    (F : (ℝ × Position) × Velocity → ℝ) (p : Phase) : physicalEvolution f F 0 p = f p := by
  simp only [physicalEvolution,neg_zero,TorusFlight.flight_zero,physicalLinearProfile_initial,
    max_eq_right (hf p)]

theorem physicalEvolution_along {f : Density} (hf : ∀ p, 0 ≤ f p)
    {F : (ℝ × Position) × Velocity → ℝ} (hF : ∀ p, 0 ≤ F p)
    {t : ℝ} (ht : 0 ≤ t) (p : Phase) :
    physicalEvolution f F t (TorusFlight.flight t p) = physicalLinearProfile f F (t,p) := by
  simp only [physicalEvolution,TorusFlight.flight_neg]
  exact max_eq_right (physicalLinearProfile_nonneg hf hF ht p)

theorem GlobalCollisionLimit.physicalEvolution_eq_density
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalEvolution f G.weakLimit.kineticProfile z.1 z.2 = G.weakLimit.density z := by
  have he := (TorusFlight.back_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    (G.linear_profile_eq_density hf hi hT)
  have ht : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase), z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [he,ht] with z hz hzt
  change max 0 (physicalLinearProfile f G.weakLimit.kineticProfile
    (z.1,TorusFlight.flight (-z.1) z.2)) = _
  have hpos : 0 ≤ physicalLinearProfile f G.weakLimit.kineticProfile
      (z.1,TorusFlight.flight (-z.1) z.2) :=
    physicalLinearProfile_nonneg (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) hzt.1 _
  rw [max_eq_right hpos]
  simpa only [TorusFlight.neg_flight,Prod.eta] using hz

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Every-time finite entropy and strong L1 traces in physical coordinates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem physicalEvolution_eq {f : Density} (hf : ∀ p, 0 ≤ f p)
    {F : (ℝ × Position) × Velocity → ℝ} (hF : ∀ p, 0 ≤ F p)
    {t : ℝ} (ht : 0 ≤ t) (p : Phase) :
    physicalEvolution f F t p = physicalLinearProfile f F (t,TorusFlight.flight (-t) p) :=
  max_eq_right (physicalLinearProfile_nonneg hf hF ht _)

theorem GlobalCollisionLimit.physical_finiteEntropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) : FiniteEntropyDatum (physicalEvolution f G.weakLimit.kineticProfile t) := by
  let U := fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)
  have he : physicalEvolution f G.weakLimit.kineticProfile t =
      (fun p => U (TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  rw [he]
  exact (G.linear_finiteEntropy hf hi ht).comp_flight (-t)

theorem GlobalCollisionLimit.physical_entropyMoment_le
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ p, entropyMoment (physicalEvolution f G.weakLimit.kineticProfile t) p) ≤ physicalEntropyBudget f := by
  have hUm : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
    ((measurable_const (a := t)).prodMk measurable_id)
  have heq : physicalEvolution f G.weakLimit.kineticProfile t =
      (fun p => physicalLinearProfile f G.weakLimit.kineticProfile
        (t,TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  rw [heq,TorusFlight.entropyMoment_integral_comp hUm (-t)]
  exact G.linear_entropyMoment_le hf hi ht

theorem GlobalCollisionLimit.physical_strong_continuous
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p : Phase =>
      physicalEvolution f G.weakLimit.kineticProfile s p-
        physicalEvolution f G.weakLimit.kineticProfile t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  have hh := TorusFlight.strong_curve_flight
    (C := fun r p => physicalLinearProfile f G.weakLimit.kineticProfile (r,p))
    (fun r hr => (G.linear_finiteEntropy hf hi hr.1).integrable) ht
    (G.linear_profile_strong_continuous hf hi hT ht)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  apply congrArg (fun g : Phase → ℝ => eLpNorm g 1 volume)
  funext p
  rw [physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf (fun _ => G.weakLimit.nonnegative _) hs.1,
    physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf (fun _ => G.weakLimit.nonnegative _) ht.1]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Damped free waiting in physical flight coordinates -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalAdvance (p : PhysicalFlightState) (s : ℝ) : PhysicalFlightState :=
  (p.1-s,(p.2.1+s • p.2.2,p.2.2))

theorem physicalAdvance_measurable :
    Measurable (fun q : PhysicalFlightState × ℝ => physicalAdvance q.1 q.2) := by
  unfold physicalAdvance
  fun_prop

def physicalWaitingWeight (C : ℝ≥0) (q : PhysicalFlightState × ℝ) : ℝ≥0∞ :=
  {q : PhysicalFlightState × ℝ | 0 < q.2 ∧ q.2 ≤ q.1.1}.indicator
    (fun q => clockSurvival C q.2) q

theorem physicalWaitingWeight_measurable (C : ℝ≥0) : Measurable (physicalWaitingWeight C) := by
  unfold physicalWaitingWeight
  exact (show Measurable (fun q : PhysicalFlightState × ℝ => clockSurvival C q.2) by
    unfold clockSurvival; fun_prop).indicator
      ((measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst))

def physicalWaitingKernel (C : ℝ≥0) : Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const PhysicalFlightState (volume : Measure ℝ))
    (fun _ q => physicalWaitingWeight C q)).map (fun q => physicalAdvance q.1 q.2)

instance physicalWaitingKernel_sFinite (C : ℝ≥0) : IsSFiniteKernel (physicalWaitingKernel C) := by
  have : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const PhysicalFlightState (volume : Measure ℝ))
      (fun _ q => physicalWaitingWeight C q)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p q
    by_cases hq : 0 < q.2 ∧ q.2 ≤ q.1.1
    · simp [physicalWaitingWeight,hq,clockSurvival]
    · simp [physicalWaitingWeight,hq]
  unfold physicalWaitingKernel
  infer_instance

theorem physicalWaitingKernel_lintegral (C : ℝ≥0) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalWaitingKernel C p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s * F (physicalAdvance p s) := by
  have hc : Measurable (fun q : PhysicalFlightState × ℝ => F (physicalAdvance q.1 q.2)) :=
    hF.comp physicalAdvance_measurable
  have hd : Measurable (Function.uncurry
      (fun (_ : PhysicalFlightState) q => physicalWaitingWeight C q)) :=
    (physicalWaitingWeight_measurable C).comp measurable_snd
  rw [physicalWaitingKernel,Kernel.lintegral_map _ physicalAdvance_measurable p hF,
    Kernel.lintegral_withDensity _ hd p hc]
  have hi : Measurable (fun q : PhysicalFlightState × ℝ =>
      physicalWaitingWeight C q*F (physicalAdvance q.1 q.2)) :=
    (physicalWaitingWeight_measurable C).mul hc
  rw [Kernel.lintegral_id_prod hi]
  change (∫⁻ s, physicalWaitingWeight C (p,s)*F (physicalAdvance p s)) = _
  rw [← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioc 0 p.1
  · simp [physicalWaitingWeight,hs,hs.1,hs.2]
  · simp [physicalWaitingWeight,hs,show ¬(0<s ∧ s≤p.1) from hs]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Bounded and linear-velocity tests of the physical time traces -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_weak_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Published.WeakL1Converges volume
      (fun n => physicalEvolution f G.weakLimit.kineticProfile (s n))
      (physicalEvolution f G.weakLimit.kineticProfile t) := by
  apply Published.weakL1_of_strong
    ((physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (G.physical_finiteEntropy hf hi ht.1).integrable
    (fun n => (G.physical_finiteEntropy hf hi (hs n).1).integrable)
  exact (G.physical_strong_continuous hf hi hT ht).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hst,Eventually.of_forall hs⟩)

theorem GlobalCollisionLimit.physical_linearMoment_weak_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t)) :
    Published.WeakL1Converges volume
      (fun n => linearMoment (physicalEvolution f G.weakLimit.kineticProfile (s n)))
      (linearMoment (physicalEvolution f G.weakLimit.kineticProfile t)) := by
  apply weak_linearMoment
    (fun n => (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (fun _ _ => physicalEvolution_nonneg _ _ _ _)
    (fun n => (G.physical_finiteEntropy hf hi (hs n).1).2.2)
    (fun n => G.physical_entropyMoment_le hf hi (hs n).1)
    ((physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      (measurable_const.prodMk measurable_id))
    (fun _ => physicalEvolution_nonneg _ _ _ _)
    (G.physical_finiteEntropy hf hi ht.1).2.2
    (G.physical_entropyMoment_le hf hi ht.1)
    (G.physical_weak_seq hf hi hT ht hs hst)

theorem GlobalCollisionLimit.physical_linear_test_seq
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Icc 0 T)
    {s : ℕ → ℝ} (hs : ∀ n, s n ∈ Icc 0 T) (hst : Tendsto s atTop (𝓝 t))
    {ψ : Phase → ℝ} (hψ : Measurable ψ) (D : ℝ)
    (hD : ∀ p, |ψ p| ≤ D*(1+‖p.2‖)) :
    Tendsto (fun n => ∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile (s n) p)
      atTop (𝓝 (∫ p, ψ p*physicalEvolution f G.weakLimit.kineticProfile t p)) := by
  let a : Phase → ℝ := fun p => ψ p/(1+‖p.2‖)
  have ham : Measurable a := hψ.div (measurable_const.add measurable_snd.norm)
  have hab p : |a p| ≤ D := by
    dsimp only [a]
    rw [abs_div,abs_of_pos (by positivity : (0:ℝ) < 1+‖p.2‖)]
    exact (div_le_iff₀ (by positivity)).mpr (hD p)
  have he (u : Phase → ℝ) : (fun p => a p*linearMoment u p) = (fun p => ψ p*u p) := by
    funext p
    dsimp only [a,linearMoment]
    field_simp
  have hh := (G.physical_linearMoment_weak_seq hf hi hT ht hs hst).2.2 a ham ⟨D,hab⟩
  simpa only [he] using hh

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One marked physical collision after waiting with a prescribed damping rate -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalMarkedCollision (b : BeamCoefficients) (endTime : ℝ) (m : HistoryMark) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.id ×ₖ (mediumMarkedKernel b m).comap
    (fun p => ((endTime-p.1,p.2.1),p.2.2)) (by fun_prop)).map
      (fun q => (q.1.1,(q.1.2.1,q.2)))

instance physicalMarkedCollision_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) : IsSFiniteKernel (physicalMarkedCollision b endTime m) := by
  unfold physicalMarkedCollision
  infer_instance

theorem physicalMarkedCollision_velocity_integral (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision b endTime m p) =
      ∫⁻ v, F (p.1,(p.2.1,v))
        ∂mediumMarkedKernel b m ((endTime-p.1,p.2.1),p.2.2) := by
  have hm : Measurable (fun q : PhysicalFlightState × V => (q.1.1,(q.1.2.1,q.2))) := by
    fun_prop
  have hc : Measurable (fun q : PhysicalFlightState × V => F (q.1.1,(q.1.2.1,q.2))) :=
    hF.comp hm
  rw [physicalMarkedCollision,Kernel.lintegral_map _ hm p hF]
  exact Kernel.lintegral_id_prod hc _ p

theorem physicalMarkedCollision_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedCollision b endTime m p) =
      mediumMarkedRate b m ((endTime-p.1,p.2.1),p.2.2)*
        ∫⁻ n : Sphere, F (p.1,(p.2.1,markedChild m p.2.2
          (b.plusPartner (endTime-p.1,p.2.1)) (b.minusPartner (endTime-p.1,p.2.1)) n.1))
          ∂sphereProbability := by
  rw [physicalMarkedCollision_velocity_integral b endTime m p hF]
  exact mediumMarkedKernel_lintegral b m _ (hF.comp (by fun_prop))

def physicalMarkedEvent (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) : Kernel PhysicalFlightState PhysicalFlightState :=
  physicalMarkedCollision b endTime m ∘ₖ physicalWaitingKernel C

instance physicalMarkedEvent_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) : IsSFiniteKernel (physicalMarkedEvent b endTime C m) := by
  unfold physicalMarkedEvent
  infer_instance

theorem physicalMarkedEvent_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
            ∂sphereProbability) := by
  rw [physicalMarkedEvent,Kernel.lintegral_comp _ _ _ hF,
    physicalWaitingKernel_lintegral C p hF.lintegral_kernel]
  apply setLIntegral_congr_fun measurableSet_Ioc
  intro s _hs
  dsimp only
  rw [physicalMarkedCollision_lintegral b endTime m _ hF]
  simp only [physicalAdvance,mediumPoint,mediumParameterState]
  rw [show endTime-(p.1-s) = endTime-p.1+s by ring]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Selected physical words lie below the full positive collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem mediumMarkedKernel_le (b : BeamCoefficients) (m : HistoryMark) :
    mediumMarkedKernel b m ≤ mediumCollisionKernel b := by
  unfold mediumCollisionKernel
  fin_cases m
  · have h : mediumMarkedKernel b 0 ≤ mediumMarkedKernel b 0+mediumMarkedKernel b 1 :=
      le_add_of_nonneg_right bot_le
    exact h.trans (le_add_of_nonneg_right bot_le)
  · have h : mediumMarkedKernel b 1 ≤ mediumMarkedKernel b 0+mediumMarkedKernel b 1 :=
      le_add_of_nonneg_left bot_le
    exact h.trans (le_add_of_nonneg_right bot_le)
  · exact le_add_of_nonneg_left bot_le

theorem physicalMarkedCollision_le (b : BeamCoefficients) (endTime : ℝ) (m : HistoryMark) :
    physicalMarkedCollision b endTime m ≤ mediumStateCollision b endTime := by
  intro p
  apply Measure.le_iff.mpr
  intro A hA
  have hm : Measurable (A.indicator (1 : PhysicalFlightState → ℝ≥0∞)) :=
    measurable_const.indicator hA
  rw [← lintegral_indicator_one hA,← lintegral_indicator_one hA,
    physicalMarkedCollision_velocity_integral b endTime m p hm,
    mediumStateCollision_lintegral b endTime p hm]
  exact lintegral_mono' (mediumMarkedKernel_le b m _) le_rfl

theorem physicalMarkedEvent_le (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) :
    physicalMarkedEvent b endTime C m ≤ mediumStateCollision b endTime ∘ₖ physicalWaitingKernel C :=
  KernelHistoryOrder.comp_mono le_rfl (physicalMarkedCollision_le b endTime m)

def physicalMarkedWord (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    List HistoryMark → Kernel PhysicalFlightState PhysicalFlightState
  | [] => Kernel.id
  | m::ms => physicalMarkedWord b endTime C ms ∘ₖ physicalMarkedEvent b endTime C m

instance physicalMarkedWord_sFinite (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) : IsSFiniteKernel (physicalMarkedWord b endTime C ms) := by
  induction ms with
  | nil => change IsSFiniteKernel Kernel.id; infer_instance
  | cons m ms ih =>
    change IsSFiniteKernel (physicalMarkedWord b endTime C ms ∘ₖ physicalMarkedEvent b endTime C m)
    infer_instance

theorem physicalMarkedWord_le (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) :
    physicalMarkedWord b endTime C ms ≤
      (mediumStateCollision b endTime ∘ₖ physicalWaitingKernel C)^ms.length := by
  induction ms with
  | nil => exact le_rfl
  | cons m ms ih =>
    simp only [physicalMarkedWord,List.length_cons,pow_succ]
    exact KernelHistoryOrder.comp_mono (physicalMarkedEvent_le b endTime C m) ih

theorem physicalMarkedWord_step (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (ms : List HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedWord b endTime C (m::ms) p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) *
          ∫⁻ n : Sphere, (∫⁻ q, F q ∂physicalMarkedWord b endTime C ms
            (mediumParameterState b endTime p (m,(s,n)))) ∂sphereProbability) := by
  rw [physicalMarkedWord,Kernel.lintegral_comp _ _ _ hF,
    physicalMarkedEvent_lintegral b endTime C m p hF.lintegral_kernel]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Time and angle parameters for a selected physical collision -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalEventMeasure : Measure EventParameter := volume.prod sphereProbability

instance physicalEventMeasure_sFinite : SFinite physicalEventMeasure := by
  unfold physicalEventMeasure
  infer_instance

def physicalParameterWeight (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter) : ℝ≥0∞ :=
  physicalWaitingWeight C (p,a.1) *
    mediumMarkedRate b m (mediumPoint endTime p a.1,p.2.2)

theorem physicalParameterWeight_measurable (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun q : PhysicalFlightState × EventParameter =>
      physicalParameterWeight b endTime C m q.1 q.2) := by
  have ht : Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) := by
    fun_prop
  exact ((physicalWaitingWeight_measurable C).comp ht).mul
    ((mediumMarkedRate_measurable b m).comp
      (((mediumPoint_measurable endTime).comp ht).prodMk (by fun_prop)))

theorem physicalParameterWeight_ne_top (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState) (a : EventParameter) :
    physicalParameterWeight b endTime C m p a ≠ ⊤ := by
  unfold physicalParameterWeight
  by_cases h : 0 < a.1 ∧ a.1 ≤ p.1
  · rw [show physicalWaitingWeight C (p,a.1) = clockSurvival C a.1 by
      simp [physicalWaitingWeight,h]]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · simp [physicalWaitingWeight,h]

theorem physicalMarkedEvent_parameters (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (m : HistoryMark) (p : PhysicalFlightState)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂physicalMarkedEvent b endTime C m p) =
      ∫⁻ a, physicalParameterWeight b endTime C m p a *
        F (mediumParameterState b endTime p (m,a)) ∂physicalEventMeasure := by
  have hs : Measurable (fun a : EventParameter => mediumParameterState b endTime p (m,a)) :=
    (mediumParameterState_measurable b endTime).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hw : Measurable (fun a : EventParameter => physicalParameterWeight b endTime C m p a) :=
    (physicalParameterWeight_measurable b endTime C m).comp
      (measurable_const.prodMk measurable_id)
  have hM : Measurable (fun a : EventParameter => physicalParameterWeight b endTime C m p a *
      F (mediumParameterState b endTime p (m,a))) := hw.mul (hF.comp hs)
  rw [physicalMarkedEvent_lintegral b endTime C m p hF,
    physicalEventMeasure,lintegral_prod _ hM.aemeasurable,
    ← lintegral_indicator measurableSet_Ioc]
  apply lintegral_congr
  intro s
  by_cases hs : s ∈ Ioc 0 p.1
  · simp only [indicator_of_mem hs,physicalParameterWeight]
    rw [show physicalWaitingWeight C (p,s) = clockSurvival C s by
      simp [physicalWaitingWeight,hs.1,hs.2]]
    have hfin : clockSurvival C s * mediumMarkedRate b m (mediumPoint endTime p s,p.2.2) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    rw [lintegral_const_mul' _ _ hfin]
    exact (mul_assoc _ _ _).symm
  · simp [physicalParameterWeight,physicalWaitingWeight,hs,
      show ¬ (0 < s ∧ s ≤ p.1) from hs]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Gain-only physical histories with a chosen damping constant -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalBeamCollision (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  physicalMarkedCollision b endTime 1+physicalMarkedCollision b endTime 2

instance physicalBeamCollision_sFinite (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (physicalBeamCollision b endTime) := by
  unfold physicalBeamCollision
  infer_instance

def physicalBeamEvent (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  physicalBeamCollision b endTime ∘ₖ physicalWaitingKernel C

instance physicalBeamEvent_sFinite (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) :
    IsSFiniteKernel (physicalBeamEvent b endTime C) := by
  unfold physicalBeamEvent
  infer_instance

theorem physicalMarkedCollision_le_beam (b : BeamCoefficients) (endTime : ℝ)
    (m : HistoryMark) (hm : m ≠ 0) :
    physicalMarkedCollision b endTime m ≤ physicalBeamCollision b endTime := by
  unfold physicalBeamCollision
  fin_cases m
  · exact False.elim (hm rfl)
  · exact le_add_of_nonneg_right bot_le
  · exact le_add_of_nonneg_left bot_le

theorem physicalMarkedEvent_le_beam (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (m : HistoryMark) (hm : m ≠ 0) :
    physicalMarkedEvent b endTime C m ≤ physicalBeamEvent b endTime C :=
  KernelHistoryOrder.comp_mono le_rfl (physicalMarkedCollision_le_beam b endTime m hm)

theorem physicalMarkedWord_le_beam (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0)
    (ms : List HistoryMark) (hm : ∀ m ∈ ms, m ≠ 0) :
    physicalMarkedWord b endTime C ms ≤ (physicalBeamEvent b endTime C)^ms.length := by
  induction ms with
  | nil => exact le_rfl
  | cons m ms ih =>
    simp only [physicalMarkedWord,List.length_cons,pow_succ]
    exact KernelHistoryOrder.comp_mono
      (physicalMarkedEvent_le_beam b endTime C m (hm m (by simp)))
      (ih (fun n hn => hm n (by simp [hn])))

theorem physicalBeamCollision_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (F : PhysicalFlightState → ℝ≥0∞) :
    (∫⁻ q, F q ∂physicalBeamCollision b endTime p) =
      (∫⁻ q, F q ∂physicalMarkedCollision b endTime 1 p)+
      (∫⁻ q, F q ∂physicalMarkedCollision b endTime 2 p) := by
  change (∫⁻ q, F q ∂(physicalMarkedCollision b endTime 1 p+
    physicalMarkedCollision b endTime 2 p)) = _
  exact lintegral_add_measure _ _ _

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Damped endpoints of the gain-only physical collision histories -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

instance physicalBeamEvent_pow_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) : IsSFiniteKernel ((physicalBeamEvent b endTime C)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    change IsSFiniteKernel (((physicalBeamEvent b endTime C)^n) ∘ₖ physicalBeamEvent b endTime C)
    infer_instance

def physicalGainEndpoint (b : BeamCoefficients) (endTime : ℝ) (C : ℝ≥0) (n : ℕ) :
    Kernel PhysicalFlightState (V × V) :=
  (Kernel.withDensity ((physicalBeamEvent b endTime C)^n)
    (fun _ p => clockSurvival C p.1)).map finishMediumFlight

instance physicalGainEndpoint_sFinite (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) : IsSFiniteKernel (physicalGainEndpoint b endTime C n) := by
  have : IsSFiniteKernel (Kernel.withDensity ((physicalBeamEvent b endTime C)^n)
      (fun _ p => clockSurvival C p.1)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold physicalGainEndpoint
  infer_instance

theorem physicalGainEndpoint_lintegral (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    {F : V × V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, F y ∂physicalGainEndpoint b endTime C n p) =
      ∫⁻ q, clockSurvival C q.1 * F (finishMediumFlight q)
        ∂((physicalBeamEvent b endTime C)^n) p := by
  have hc : Measurable (Function.uncurry (fun (_ : PhysicalFlightState) (q : PhysicalFlightState) =>
      clockSurvival C q.1)) := by unfold clockSurvival; fun_prop
  have hf : Measurable (fun q : PhysicalFlightState => F (finishMediumFlight q)) :=
    hF.comp finishMediumFlight_measurable
  rw [physicalGainEndpoint,Kernel.lintegral_map _ finishMediumFlight_measurable p hF,
    Kernel.lintegral_withDensity _ hc p hf]

theorem physicalGainEndpoint_apply (b : BeamCoefficients) (endTime : ℝ)
    (C : ℝ≥0) (n : ℕ) (p : PhysicalFlightState)
    {A : Set (V × V)} (hA : MeasurableSet A) :
    physicalGainEndpoint b endTime C n p A =
      ∫⁻ q, clockSurvival C q.1 * A.indicator 1 (finishMediumFlight q)
        ∂((physicalBeamEvent b endTime C)^n) p := by
  rw [← lintegral_indicator_one hA]
  exact physicalGainEndpoint_lintegral b endTime C n p (measurable_const.indicator hA)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Every-time joint entropy inequality for the actual physical evolution -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_entropy_dissipation
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (relativeEntropy (physicalEvolution f G.weakLimit.kineticProfile t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (physicalEvolution f G.weakLimit.kineticProfile s)) ≤
      ENNReal.ofReal (relativeEntropy f) := by
  let E := physicalEvolution f G.weakLimit.kineticProfile
  have hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2) :=
    physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable
  have hD := physical_dissipation_eq_rate hEm
    (fun _ _ => physicalEvolution_nonneg _ _ _ _)
    G.weakLimit.kineticProfile_measurable (G.physicalEvolution_eq_density hf hi ht)
  rw [hD,relativeEntropy_eq_lintegral (G.physical_finiteEntropy hf hi ht)]
  have he : E t = (fun p => physicalLinearProfile f G.weakLimit.kineticProfile
      (t,TorusFlight.flight (-t) p)) :=
    funext (physicalEvolution_eq (F := G.weakLimit.kineticProfile) hf
      (fun _ => G.weakLimit.nonnegative _) ht)
  dsimp only [E] at he
  have hUm : Measurable (fun p : Phase => physicalLinearProfile f G.weakLimit.kineticProfile (t,p)) :=
    (physicalLinearProfile_measurable hfm G.weakLimit.kineticProfile_measurable).comp
      ((measurable_const (a := t)).prodMk measurable_id)
  rw [he,TorusFlight.scalar_entropy_lintegral_comp hUm (-t)]
  exact G.linear_joint_entropy hf hi ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exact scaling of the mixed and quadratic parts of the hot collision source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem collisionSource_const_mul (b a : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    collisionSource b (fun z => a*f z) p = a^2*collisionSource b f p := by
  unfold collisionSource
  rw [cutoffGain_const_mul,cutoffFrequency_const_mul]
  ring

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem collisionSource_base_comp (b : ℝ) (f : X × Velocity → ℝ) (τ : Y → X)
    (p : Y × Velocity) :
    collisionSource b (fun z => f (τ z.1,z.2)) p = collisionSource b f (τ p.1,p.2) := rfl

theorem mixed_source_rescale (b r : ℝ) (hr : r ≠ 0) (c h : X × Velocity → ℝ)
    (p : X × Velocity) :
    2*mixedGainDensity b (fun z => r*c z) (fun z => r⁻¹*h z) p-
        (r⁻¹*h p)*KineticCollisionNullSets.frequency b (fun z => r*c z) p+
        r^2*collisionSource b (fun z => r⁻¹*h z) p =
      2*mixedGainDensity b c h p-h p*KineticCollisionNullSets.frequency b c p+
        collisionSource b h p := by
  rw [mixedGain_const_mul,cutoffFrequency_const_mul,collisionSource_const_mul]
  field_simp

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Full physical gain and loss depend only on the spacetime density class -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness

theorem physical_gainLoss_eq {F : Evolution}
    {g : (ℝ × Position) × Velocity → ℝ} {T : ℝ}
    (hFm : Measurable (fun z : ℝ × Phase => F z.1 z.2)) (hgm : Measurable g)
    (he : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      F z.1 z.2 = g ((z.1,z.2.1),z.2.2)) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      gain (F z.1) z.2.1 z.2.2 = CollisionCompactness.gainDensity g ((z.1,z.2.1),z.2.2) ∧
      loss (F z.1) z.2.1 z.2.2 = CollisionCompactness.lossDensity g ((z.1,z.2.1),z.2.2) := by
  have hkin : Measurable (kineticDensity F) := hFm.comp MeasurableEquiv.prodAssoc.measurable
  have hekin : kineticDensity F =ᵐ[
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)] g :=
    (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae he
  have hc := CollisionCompactness.gainLoss_congr hkin hgm hekin
  have hh := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae
    (hc.1.and hc.2)
  filter_upwards [hh] with z hz
  exact ⟨(kineticDensity_gain F z).symm.trans hz.1,(kineticDensity_loss F z).symm.trans hz.2⟩

end BoltzmannNonuniqueness

end

end

section

/-! # Physical collision fibers and separate normalized gain/loss integrability -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.physical_spacetime_entropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (T : ℝ) :
    Integrable (fun z : ℝ × Phase =>
      entropyMoment (physicalEvolution f G.weakLimit.kineticProfile z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume) :=
  entropyMoment_spacetime_integrable
    (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable)
    (fun _ _ => physicalEvolution_nonneg _ _ _ _)
    (fun _ ht => G.physical_finiteEntropy hf hi ht.1)
    ⟨physicalEntropyBudget f,fun _ ht => G.physical_entropyMoment_le hf hi ht.1⟩

theorem GlobalCollisionLimit.physical_kinetic_entropy
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (T : ℝ) :
    Integrable (entropyGauge (kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)))
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable
    (G.physical_spacetime_entropy hf hi T)

theorem GlobalCollisionLimit.physical_kinetic_dissipation_lt_top
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))
      (kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)) < ⊤ := by
  have hEm := physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable
  have hDn : (∫⁻ s in Icc (0:ℝ) T,
      entropyDissipation (physicalEvolution f G.weakLimit.kineticProfile s)) ≤
      ENNReal.ofReal (relativeEntropy f) :=
    (le_add_of_nonneg_left zero_le).trans (G.physical_entropy_dissipation hf hi hT)
  change rateDissipation (AnnularEnvelope.timePositionVolume T)
    (kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)) < ⊤
  rw [kineticDensity_rateDissipation hEm (fun _ _ => physicalEvolution_nonneg _ _ _ _) T]
  exact hDn.trans_lt ENNReal.ofReal_lt_top

theorem GlobalCollisionLimit.physical_kinetic_collision_integrability
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    let g := kineticDensity (physicalEvolution f G.weakLimit.kineticProfile)
    let μ := (volume.restrict (Icc 0 T)).prod (volume : Measure Position)
    Integrable (fun p => gainDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
    Integrable (fun p => lossDensity g p/(1+g p/maxwellian p.2)) (μ.prod volume) ∧
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      Integrable (fun q => postRate g (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q => preRate g (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) := by
  dsimp only
  apply normalized_collisions_of_entropy
    (μ := (volume.restrict (Icc 0 T)).prod (volume : Measure Position))
    (g := kineticDensity (physicalEvolution f G.weakLimit.kineticProfile))
  · exact measurable_kineticDensity
      (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable)
  · intro p
    change 0 ≤ physicalEvolution f G.weakLimit.kineticProfile p.1.1 (p.1.2,p.2)
    exact physicalEvolution_nonneg _ _ _ _
  · exact G.physical_kinetic_entropy hf hi T
  · exact G.physical_kinetic_dissipation_lt_top hf hi hT

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The characteristic source is the physical nonlinear collision source -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.linear_source_eq_physical_collision
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase),
      physicalCharacteristicGain G.weakLimit.kineticProfile z-
        physicalCharacteristicFrequency G.weakLimit.kineticProfile z*
          physicalLinearProfile f G.weakLimit.kineticProfile z =
      collision (physicalEvolution f G.weakLimit.kineticProfile z.1)
        (TorusFlight.flight z.1 z.2).1 (TorusFlight.flight z.1 z.2).2 := by
  let F := G.weakLimit.kineticProfile
  have he := physical_gainLoss_eq
    (physicalEvolution_measurable hfm G.weakLimit.kineticProfile_measurable)
    G.weakLimit.kineticProfile_measurable (G.physicalEvolution_eq_density hf hi hT)
  have ha := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae he
  have hb := (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
    (volume : Measure Velocity)).quasiMeasurePreserving.ae
      (G.normalized_integrability hf hi hT).2.2
  filter_upwards [ha,hb,G.linear_profile_eq_density hf hi hT] with z hz hfib hu
  let y : (ℝ × Position) × Velocity := ((z.1,(TorusFlight.flight z.1 z.2).1),z.2.2)
  have hl : lossDensity F y = F y*kineticFrequency F y :=
    lossDensity_eq_mul_kineticFrequency F y hfib.2
  have hu' : physicalLinearProfile f F z = F y := hu
  change gainDensity F y-kineticFrequency F y*physicalLinearProfile f F z = _
  unfold collision
  rw [hz.1,hz.2]
  change gainDensity F y-kineticFrequency F y*physicalLinearProfile f F z =
    gainDensity F y-lossDensity F y
  rw [hl,hu']
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Global weak continuity of the physical evolution -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_weak_continuity
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {ψ : Phase → ℝ} (hψ : Measurable ψ) (hb : ∃ C : ℝ, ∀ p, |ψ p| ≤ C) :
    ContinuousOn (fun t => ∫ p, physicalEvolution f G.weakLimit.kineticProfile t p*ψ p) (Ici 0) := by
  intro t ht
  have ht0 : 0 ≤ t := ht
  apply tendsto_iff_seq_tendsto.mpr
  intro s hs
  have hbounds : ∀ᶠ n in atTop, s n ∈ Icc 0 (t+1) := by
    filter_upwards [eventually_mem_of_tendsto_nhdsWithin hs,
      (tendsto_nhds_of_tendsto_nhdsWithin hs).eventually
        (gt_mem_nhds (show t < t+1 by linarith))] with n hn hn'
    exact ⟨hn,hn'.le⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbounds
  have hh := G.physical_weak_seq hf hi (show 0 ≤ t+1 by linarith)
    (show t ∈ Icc 0 (t+1) from ⟨ht,by linarith⟩)
    (fun n => hN (n+N) (Nat.le_add_left N n))
    ((tendsto_nhds_of_tendsto_nhdsWithin hs).comp (tendsto_add_atTop_nat N))
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa only [mul_comm,Function.comp_def] using hh.2.2 ψ hψ hb

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Exact nonlinear renormalized integrand along the physical characteristics -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_renormalized_field_along
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (β : Renormalization) (φ : KineticTest) :
    TorusFlight.along (renormalizedIntegrand (physicalEvolution f G.weakLimit.kineticProfile) β φ)
      =ᵐ[(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
        linearRenormalizedField f G.weakLimit.kineticProfile β φ := by
  have ht : ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase), z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [G.linear_source_eq_physical_collision hf hi hT,ht] with z hz ht
  dsimp only [TorusFlight.along,renormalizedIntegrand,relativeDensity,linearRenormalizedField]
  rw [physicalEvolution_along (F := G.weakLimit.kineticProfile) hf
    (fun _ => G.weakLimit.nonnegative _) ht.1,← hz]
  rfl

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single almost-everywhere comparison of the physical evolution and weak limit -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalCollisionLimit.physical_eq_density_ae
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t →
      physicalEvolution f G.weakLimit.kineticProfile t =ᵐ[volume]
        (fun p => G.weakLimit.density (t,p)) := by
  have hh n := Measure.ae_ae_of_ae_prod
    (G.physicalEvolution_eq_density hf hi (Nat.cast_nonneg n))
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  filter_upwards [ae_all_iff.mpr hh] with t ht
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact ht n ⟨ht0,hn⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
