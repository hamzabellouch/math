import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildConservation
import OAI.MathematicalPhysics.Boltzmann.Branching.EnergyTruncation
import OAI.MathematicalPhysics.Boltzmann.Branching.FullDissipationLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.SmoothTestFamily
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocitySmoothingError
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedPairCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairPatchCover
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicMomentEntropy
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicRenormalizedCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicWeakCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakLinearMomentLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # The actual global density and normalized pair on one averaging subsequence -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_global_density_pair_with_patch_averages
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (χ : ℕ → Published.SpaceTime → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχs : ∀ j, tsupport (χ j) ⊆ TorusKineticChart.interiorRegion)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    ∃ (G : GlobalWeakLimit f hfm) (W : (ℝ × Position) × (Velocity × Velocity) → ℝ),
      Published.WeakL1Converges
        ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm (G.indices n)).kineticProfile) W ∧
      ∀ s i, Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0) := by
  obtain ⟨G,hG⟩ := exists_globalWeakLimit_patch_averages f hfm hf hi χ hχ hχc hχs ψ hψ hψc
  obtain ⟨φ,hφ,W,hW⟩ := G.exists_normalizedPair_limit hf hi
  refine ⟨G.subsequence hφ,W,hW,fun s i => ?_⟩
  have hc := (hG s i).comp hφ.tendsto_atTop
  exact hc

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Localized weak convergence of the actual lifted densities -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.localized_weak {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) {T C : ℝ} (hT : 0 ≤ T)
    {w : Published.KineticPhase → ℝ} (hw : Measurable w) (hb : ∀ z, |w z| ≤ C)
    (hs : ∀ z, z ∉ TorusKineticChart.region T → w z = 0) :
    Published.WeakL1Converges volume
      (fun n z => w z*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile z)
      (fun z => w z*TorusKineticChart.liftDensity G.kineticProfile z) := by
  have h := (G.lifted_weak_on_window hT).bounded_mul hw C hb
  rw [TorusKineticChart.cellVolume_eq] at h
  apply h.of_restrict_support (TorusKineticChart.measurableSet_region T)
  · intro n z hz
    rw [hs z hz,zero_mul]
  · intro z hz
    rw [hs z hz,zero_mul]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong mass convergence on an actual periodic spacetime patch -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.patch_mass_strong {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T C : ℝ} (hT : 0 ≤ T) {χ : Published.SpaceTime → ℝ}
    (hχ : Measurable χ) (hC : ∀ z, |χ z| ≤ C)
    (hχs : ∀ z, z ∉ Icc 0 T ×ˢ TorusChart.cube → χ z = 0)
    (hc : ∀ j, Tendsto (fun n => eLpNorm (fun z =>
      χ z*(∫ v, Compactness.velocityExhaustion j v*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ z*(∫ v, Compactness.velocityExhaustion j v*TorusKineticChart.liftDensity
        G.kineticProfile (z,v))) 1 volume) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z =>
      χ z*(∫ v, TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
      atTop (𝓝 0) := by
  let F : ℕ → Published.KineticPhase → ℝ := fun n z => χ z.1*TorusKineticChart.liftDensity
    (approximatingSolution f hfm (G.indices n)).kineticProfile z
  let g : Published.KineticPhase → ℝ := fun z => χ z.1*TorusKineticChart.liftDensity G.kineticProfile z
  have hFm n : Measurable (F n) := (hχ.comp measurable_fst).mul
    (TorusKineticChart.liftDensity_measurable
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
  have hs (z : Published.KineticPhase) (hz : z ∉ TorusKineticChart.region T) : χ z.1 = 0 := by
    apply hχs
    intro h
    exact hz ⟨h,mem_univ _⟩
  have hFi n : Integrable (F n) := TorusKineticChart.cutoff_liftDensity_integrable
    (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
    (hχ.comp measurable_fst)
    (memLp_one_iff_integrable.mp ((approximatingSolution_compactness_hypotheses f hfm hf hi
      (volume.restrict (Icc 0 T))).1.memLp (G.indices n)))
    (fun z => hC z.1) hs
  have hw : Published.WeakL1Converges (volume.prod volume) F g :=
    G.localized_weak hT (hχ.comp measurable_fst) (fun z => hC z.1) hs
  have h := Compactness.strong_mass_of_velocity_averages hFm hFi hw
    (fun j => (Compactness.velocityExhaustion_smooth j).continuous.measurable)
    (fun j v => by rw [abs_of_nonneg (Compactness.velocityExhaustion_nonneg j v)];
                   exact Compactness.velocityExhaustion_le_one j v)
    (Compactness.velocityExhaustion_error_tendsto
      (C*((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)))
    (fun j n => approximatingSolution_patch_velocity_tail f hfm hf hi (by positivity)
      hχ hC hχs (Compactness.velocityExhaustion_smooth j).continuous.measurable
      (Compactness.velocityExhaustion_nonneg j) (Compactness.velocityExhaustion_le_one j)
      (Compactness.velocityExhaustion_eq_one j) (G.indices n))
    (fun j => ?_)
  · simpa only [F,g,integral_const_mul] using h
  · have he (z : Published.SpaceTime) (v : Velocity) (a : ℝ) :
        Compactness.velocityExhaustion j v*(χ z*a) = χ z*(Compactness.velocityExhaustion j v*a) := by ring
    simpa only [F,g,he,integral_const_mul] using hc j

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual finite approximations retain the original energy bound -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem approximatingSolution_energy_le (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n : ℕ) (t : ℝ) :
    energy (fun p => (approximatingSolution f hfm n).density (t,p)) ≤ energy f := by
  let S := approximatingSolution f hfm n
  have he : (fun p => S.density (t,p)) =
      (fun p => S.density (PositiveIntegral.time ((n:ℝ)+1) t,p)) :=
    funext (S.density_clipped (by positivity) t)
  rw [he,S.energy_conservation (by positivity) (PositiveIntegral.time_bounds (by positivity) t)]
  exact integral_mono (initialApproximation_finiteEntropy (by positivity) hfm).integrable_energy
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable_energy
    (fun p => mul_le_mul_of_nonneg_left (initialApproximation_le hf p) (sq_nonneg _))

theorem approximatingSolution_truncated_energy_le (f : Density) (hfm : Measurable f)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) (n k : ℕ) (t : ℝ) :
    (∫ p, truncatedEnergyWeight k p*(approximatingSolution f hfm n).density (t,p)) ≤ energy f := by
  let S := approximatingSolution f hfm n
  have hfinite := S.finiteEntropy (by positivity) t
  apply le_trans (integral_mono (truncatedEnergy_integrable hfinite.integrable k)
    hfinite.integrable_energy (fun p => mul_le_mul_of_nonneg_right
      (min_le_left _ _) (S.nonnegative _)))
  exact approximatingSolution_energy_le f hfm hf hi n t

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The sharp energy bound passes to the same global weak density -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.truncated_energy_ae_on_window
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (k : ℕ) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p, truncatedEnergyWeight k p*G.density (t,p)) ≤ energy f := by
  let μ := volume.restrict (Icc 0 T)
  have hfi n : Integrable (approximatingSolution f hfm (G.indices n)).density (μ.prod volume) :=
    density_integrable_of_spacetimeEntropy (approximatingSolution f hfm (G.indices n)).measurable
      (approximatingSolution f hfm (G.indices n)).nonnegative
      (approximatingSolution_spacetimeEntropy_integrable f hfm hf hi (G.indices n) μ)
  have hm : Measurable (fun z : ℝ × Phase => truncatedEnergyWeight k z.2) :=
    (truncatedEnergyWeight_measurable k).comp measurable_snd
  have hb (z : ℝ × Phase) : |truncatedEnergyWeight k z.2| ≤ (k:ℝ) := truncatedEnergyWeight_abs_le k z.2
  have hw := (G.weak_on_window hT).marginal hfi hm k hb
  exact hw.le
    (fun n => ((hfi n).bdd_mul hm.aestronglyMeasurable (ae_of_all _ hb)).integral_prod_left)
    measurable_const (integrable_const _) (fun n => ae_of_all _
      (fun t => approximatingSolution_truncated_energy_le f hfm hf hi (G.indices n) k t))

theorem GlobalWeakLimit.energy_ae
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∀ᵐ t ∂volume, 0 ≤ t → energy (fun p => G.density (t,p)) ≤ energy f := by
  have hh (n k : ℕ) := G.truncated_energy_ae_on_window hf hi (Nat.cast_nonneg n) k
  simp only [ae_restrict_iff' measurableSet_Icc] at hh
  have hall := ae_all_iff.mpr (fun n => ae_all_iff.mpr (hh n))
  filter_upwards [hall,G.finiteEntropy_ae_volume hf hi] with t ht hd
  intro ht0
  obtain ⟨n,hn⟩ := exists_nat_ge t
  exact energy_le_of_truncated (G.measurable.comp (measurable_const.prodMk measurable_id))
    (fun p => G.nonnegative (t,p)) hd.1
    (integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (hf p)))
    (fun k => ht n k ⟨ht0,hn⟩)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual global density/pair subsequence has strong local mass averages -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

private theorem patch_bounds {χ : Published.SpaceTime → ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ TorusKineticChart.interiorRegion) :
    ∃ T C : ℝ, 0 ≤ T ∧ (∀ z, |χ z| ≤ C) ∧
      (∀ z, z ∉ Icc 0 T ×ˢ TorusChart.cube → χ z = 0) := by
  obtain ⟨T,hT,hball⟩ := hc.isBounded.subset_ball_lt 0 (0 : Published.SpaceTime)
  obtain ⟨C,hC⟩ := hχ.bounded_above_of_compact_support hc
  refine ⟨T,C,hT.le,hC,fun z hz => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro hzs
  have ht := hs hzs
  have hn : ‖z‖ < T := by simpa only [Metric.mem_ball,dist_zero_right] using hball hzs
  have hcoord : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  exact hz ⟨⟨le_of_lt ht.1,(le_abs_self _).trans (hcoord.trans hn.le)⟩,interior_subset ht.2⟩

theorem exists_global_density_pair_with_strong_mass
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    (χ : ℕ → Published.SpaceTime → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hχc : ∀ j, HasCompactSupport (χ j))
    (hχs : ∀ j, tsupport (χ j) ⊆ TorusKineticChart.interiorRegion)
    (ψ : ℕ → Velocity → ℝ)
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i)) :
    ∃ (G : GlobalWeakLimit f hfm) (W : (ℝ × Position) × (Velocity × Velocity) → ℝ),
      Published.WeakL1Converges
        ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm (G.indices n)).kineticProfile) W ∧
      (∀ s i, Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0)) ∧
      (∀ s, Tendsto (fun n => eLpNorm (fun z =>
        χ s z*(∫ v, TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
        χ s z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
        atTop (𝓝 0)) := by
  let tests : ℕ → Velocity → ℝ := fun n => if (Nat.unpair n).1 = 0
    then Compactness.velocityExhaustion (Nat.unpair n).2 else ψ (Nat.unpair n).2
  have htests n : ContDiff ℝ (⊤ : ℕ∞) (tests n) := by
    dsimp only [tests]
    split_ifs
    · exact Compactness.velocityExhaustion_smooth _
    · exact hψ _
  have htestsc n : HasCompactSupport (tests n) := by
    dsimp only [tests]
    split_ifs
    · exact Compactness.velocityExhaustion_compact _
    · exact hψc _
  obtain ⟨G,W,hW,havg⟩ := exists_global_density_pair_with_patch_averages
    f hfm hf hi χ hχ hχc hχs tests htests htestsc
  refine ⟨G,W,hW,fun s i => ?_,fun s => ?_⟩
  · simpa only [tests,Nat.unpair_pair,one_ne_zero,ite_false] using havg s (Nat.pair 1 i)
  · obtain ⟨T,C,hT,hC,hs⟩ := patch_bounds (hχ s).continuous (hχc s) (hχs s)
    apply G.patch_mass_strong hf hi hT (hχ s).continuous.measurable hC hs
    intro j
    simpa only [tests,Nat.unpair_pair,ite_true] using havg s (Nat.pair 0 j)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Identification of the actual normalized collision-pair weak limit -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.normalizedPair_identified_on_window
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {W : (ℝ × Position) × (Velocity × Velocity) → ℝ}
    (hW : Published.WeakL1Converges
      ((finiteTimeMeasure.prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume
        (approximatingSolution f hfm (G.indices n)).kineticProfile) W)
    {χ : ℕ → Published.SpaceTime → ℝ}
    (hχ : ∀ j, Measurable (χ j))
    (hcover : ∀ z ∈ TorusKineticChart.interiorRegion, ∃ j, χ j z ≠ 0)
    {ψ : ℕ → Velocity → ℝ}
    (hψ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (ψ i)) (hc : ∀ i, HasCompactSupport (ψ i))
    (hdet : ∀ u : Velocity → ℝ, Integrable u → (∀ i, ∫ v, ψ i v*u v = 0) → u =ᵐ[volume] 0)
    (ha : ∀ s i, Tendsto (fun n => eLpNorm (fun z =>
      χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ s z*(∫ v, ψ i v*TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
      atTop (𝓝 0))
    (hr : ∀ s, Tendsto (fun n => eLpNorm (fun z =>
      χ s z*(∫ v, TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ s z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
      atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) :
    TorusKineticChart.liftPair W =ᵐ[(TorusKineticChart.baseVolume T).prod (volume.prod volume)]
      Compactness.normalizedPair volume (TorusKineticChart.liftDensity G.kineticProfile) := by
  let F : ℕ → Published.KineticPhase → ℝ := fun n => TorusKineticChart.liftDensity
    (approximatingSolution f hfm (G.indices n)).kineticProfile
  let g := TorusKineticChart.liftDensity G.kineticProfile
  have hFm n : Measurable (F n) := TorusKineticChart.liftDensity_measurable
    (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
  have hgm : Measurable g := TorusKineticChart.liftDensity_measurable G.kineticProfile_measurable
  have hFn n z : 0 ≤ F n z := (approximatingSolution f hfm (G.indices n)).nonnegative _
  have hgn z : 0 ≤ g z := G.nonnegative _
  have hFi n : Integrable (F n) ((TorusKineticChart.baseVolume T).prod volume) :=
    integrable_of_entropyGauge (hFm n) (hFn n)
      (approximatingSolution_cell_entropy_integrable f hfm hf hi T (G.indices n))
  have hgi : Integrable g ((TorusKineticChart.baseVolume T).prod volume) :=
    (G.lifted_weak_on_window hT).2.1
  have hp := normalizedPair_lifted_weak
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable) hW hT
  have hm := Compactness.uniformIntegrable_comp
    (approximatingSolution_cell_mass_uniformIntegrable f hfm hf hi T) G.indices
  have hbase : TorusKineticChart.baseVolume T ≤ (volume : Measure Published.SpaceTime) :=
    Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hlocal {a : ℕ → Published.SpaceTime → ℝ}
      (h : Tendsto (fun n => eLpNorm (a n) 1 volume) atTop (𝓝 0)) :
      Tendsto (fun n => eLpNorm (a n) 1 (TorusKineticChart.baseVolume T)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
      (fun n => eLpNorm_mono_measure (a n) hbase)
  apply Compactness.pair_ae_of_patch_cover
    (TorusKineticChart.liftPair_measurable hW.1)
    (Compactness.normalizedTensor_measurable
      (Compactness.fiberMass_measurable (ν := volume) hgm) hgm hgm) hχ
  · exact (TorusKineticChart.interiorRegion_ae T).mono (fun z hz => hcover z hz)
  · intro j k
    apply Compactness.normalizedPair_eq_on_patch hFm hFn hFi hgm hgn hgi hp hm
      (measurableSet_le measurable_const (hχ j).abs) (by positivity)
      (fun _ h => h)
    · exact hlocal (hr j)
    · exact hψ
    · exact hc
    · exact hdet
    · exact fun i => hlocal (ha j i)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Strong spatial mass convergence on every full periodic time window -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.lifted_mass_strong_of_patches
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {χ : ℕ → Published.SpaceTime → ℝ} (hχ : ∀ j, Measurable (χ j))
    (hcover : ∀ z ∈ TorusKineticChart.interiorRegion, ∃ j, χ j z ≠ 0)
    (hr : ∀ j, Tendsto (fun n => eLpNorm (fun z =>
      χ j z*(∫ v, TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ j z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
      atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => eLpNorm (fun z =>
      Compactness.fiberMass volume (TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile) z-
      Compactness.fiberMass volume (TorusKineticChart.liftDensity G.kineticProfile) z)
      1 (TorusKineticChart.baseVolume T)) atTop (𝓝 0) := by
  apply Compactness.strongL1_of_nonzero_patches
  · exact fun n => Compactness.fiberMass_measurable (ν := volume)
      (TorusKineticChart.liftDensity_measurable
        (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
  · exact Compactness.fiberMass_measurable (ν := volume)
      (TorusKineticChart.liftDensity_measurable G.kineticProfile_measurable)
  · exact Compactness.uniformIntegrable_comp
      (approximatingSolution_cell_mass_uniformIntegrable f hfm hf hi T) G.indices
  · exact (G.lifted_weak_on_window hT).2.1.integral_prod_left
  · exact hχ
  · exact (TorusKineticChart.interiorRegion_ae T).mono (fun z hz => hcover z hz)
  · intro j
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hr j)
      (fun _ => zero_le)
    intro n
    exact eLpNorm_mono_measure _
      (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)

theorem GlobalWeakLimit.mass_strong_of_patches
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {χ : ℕ → Published.SpaceTime → ℝ} (hχ : ∀ j, Measurable (χ j))
    (hcover : ∀ z ∈ TorusKineticChart.interiorRegion, ∃ j, χ j z ≠ 0)
    (hr : ∀ j, Tendsto (fun n => eLpNorm (fun z =>
      χ j z*(∫ v, TorusKineticChart.liftDensity
        (approximatingSolution f hfm (G.indices n)).kineticProfile (z,v))-
      χ j z*(∫ v, TorusKineticChart.liftDensity G.kineticProfile (z,v))) 1 volume)
      atTop (𝓝 0))
    {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun n => eLpNorm (fun z =>
      Compactness.fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile z-
      Compactness.fiberMass volume G.kineticProfile z)
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0) := by
  have ht := G.lifted_mass_strong_of_patches hf hi hχ hcover hr hT
  let c : ℝ × Position → Published.SpaceTime := fun z => (z.1,TorusChart.representative z.2)
  have hc : MeasurePreserving c
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))
      (TorusKineticChart.baseVolume T) :=
    (MeasurePreserving.id _).prod TorusChart.representative_measurePreserving
  have he n : eLpNorm (fun z =>
      Compactness.fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile z-
      Compactness.fiberMass volume G.kineticProfile z)
      1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) =
      eLpNorm (fun z =>
        Compactness.fiberMass volume (TorusKineticChart.liftDensity
          (approximatingSolution f hfm (G.indices n)).kineticProfile) z-
        Compactness.fiberMass volume (TorusKineticChart.liftDensity G.kineticProfile) z)
        1 (TorusKineticChart.baseVolume T) := by
    have hm := (Compactness.fiberMass_measurable (ν := volume)
      (TorusKineticChart.liftDensity_measurable
        (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)).sub
      (Compactness.fiberMass_measurable (ν := volume)
        (TorusKineticChart.liftDensity_measurable G.kineticProfile_measurable))
    convert eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hc using 1
    simp only [Function.comp_def,c,Pi.sub_apply,Compactness.fiberMass,TorusKineticChart.liftDensity,
      TorusChart.projection_representative]
  simpa only [he] using ht

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual global limit retains both strong masses and normalized pairs -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_globalWeakLimit_with_strong_mass_pairs
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm,
      (∀ T : ℝ, 0 ≤ T → Tendsto (fun n => eLpNorm (fun z =>
        Compactness.fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile z-
        Compactness.fiberMass volume G.kineticProfile z)
        1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0)) ∧
      (∀ T : ℝ, 0 ≤ T → Published.WeakL1Converges
        (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (Compactness.normalizedPair volume G.kineticProfile)) := by
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    TorusKineticChart.interiorRegion_open TorusKineticChart.interiorRegion_nonempty
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  obtain ⟨G,W,hW,ha,hr⟩ := exists_global_density_pair_with_strong_mass
    f hfm hf hi χ hχ hχc hχs ψ hψ hψc
  refine ⟨G,fun T hT => G.mass_strong_of_patches hf hi
    (fun j => (hχ j).continuous.measurable) hcover hr hT, fun T hT => ?_⟩
  have he := G.normalizedPair_identified_on_window hf hi hW
    (fun j => (hχ j).continuous.measurable) hcover hψ hψc hdet ha hr hT
  rw [normalizedPair_lift] at he
  have he' : W =ᵐ[(((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))]
      Compactness.normalizedPair volume G.kineticProfile := by
    have h := (TorusKineticChart.pair_measurePreserving T).quasiMeasurePreserving.ae_eq_comp he
    simpa only [TorusKineticChart.liftPair_comp,AnnularEnvelope.timePositionVolume,
      Measure.volume_eq_prod] using h
  exact (weak_pair_on_window hW hT).congr_limit
    (Compactness.normalizedTensor_measurable
      (Compactness.fiberMass_measurable (ν := volume) G.kineticProfile_measurable)
      G.kineticProfile_measurable G.kineticProfile_measurable) he'

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual global weak limit with all normalized velocity pairs identified -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem exists_globalWeakLimit_with_normalized_pairs
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.normalizedPair volume
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (Compactness.normalizedPair volume G.kineticProfile) := by
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    TorusKineticChart.interiorRegion_open TorusKineticChart.interiorRegion_nonempty
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  obtain ⟨G,W,hW,ha,hr⟩ := exists_global_density_pair_with_strong_mass
    f hfm hf hi χ hχ hχc hχs ψ hψ hψc
  refine ⟨G,fun T hT => ?_⟩
  have he := G.normalizedPair_identified_on_window hf hi hW
    (fun j => (hχ j).continuous.measurable) hcover hψ hψc hdet ha hr hT
  rw [normalizedPair_lift] at he
  have he' : W =ᵐ[(((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))]
      Compactness.normalizedPair volume G.kineticProfile := by
    have h := (TorusKineticChart.pair_measurePreserving T).quasiMeasurePreserving.ae_eq_comp he
    simpa only [TorusKineticChart.liftPair_comp,AnnularEnvelope.timePositionVolume,
      Measure.volume_eq_prod] using h
  exact (weak_pair_on_window hW hT).congr_limit
    (Compactness.normalizedTensor_measurable
      (Compactness.fiberMass_measurable (ν := volume) G.kineticProfile_measurable)
      G.kineticProfile_measurable G.kineticProfile_measurable) he'

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual periodic normalized pairs converge with the collision velocity weight -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.kinetic_entropy_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (entropyGauge G.kineticProfile)
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) :=
  (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable
    (G.entropyMoment_on_window hf hi hT)

theorem GlobalWeakLimit.weightedPair_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T)
    (hp : Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume
        (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (Compactness.normalizedPair volume G.kineticProfile)) :
    Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.weightedNormalizedPair
        (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (Compactness.weightedNormalizedPair G.kineticProfile) := by
  apply Compactness.weak_weightedNormalizedPair
    (C := max ((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)
      (∫ p, entropyGauge G.kineticProfile p
        ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume))
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    (fun n _ => (approximatingSolution f hfm (G.indices n)).nonnegative _)
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  · intro n
    exact ((approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity)
      (approximatingSolution_entropy f hfm hf hi _)).trans (le_max_left _ _)
  · exact G.kineticProfile_measurable
  · exact fun _ => G.nonnegative _
  · exact G.kinetic_entropy_on_window hf hi hT
  · exact le_max_right _ _
  · exact hp

theorem exists_globalWeakLimit_with_weighted_pairs
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
        (fun n => Compactness.weightedNormalizedPair
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (Compactness.weightedNormalizedPair G.kineticProfile) := by
  obtain ⟨G,hG⟩ := exists_globalWeakLimit_with_normalized_pairs f hfm hf hi
  exact ⟨G,fun T hT => G.weightedPair_on_window hf hi hT (hG T hT)⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual global density converges against all linearly growing tests -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.weak_linearMoment_on_window {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)
      (fun n => linearMoment (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (linearMoment G.kineticProfile) := by
  let μ := ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume : Measure Velocity)
  let C := max ((volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f)
    (∫ p, entropyGauge G.kineticProfile p ∂μ)
  apply weak_linearMoment (C := C)
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    (fun n _ => (approximatingSolution f hfm (G.indices n)).nonnegative _)
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  · intro n
    exact ((approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)).trans
      (le_max_left _ _)
  · exact G.kineticProfile_measurable
  · exact fun _ => G.nonnegative _
  · exact G.kinetic_entropy_on_window hf hi hT
  · exact le_max_right _ _
  · exact G.kinetic_weak_on_window hT

theorem GlobalWeakLimit.linear_test_tendsto {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) {ψ : ℝ × Phase → ℝ} (hψ : Measurable ψ) (C : ℝ)
    (hC : ∀ z, |ψ z| ≤ C*(1+‖z.2.2‖)) :
    Tendsto (fun n => ∫ z, ψ z*(approximatingSolution f hfm (G.indices n)).density z
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) atTop
      (𝓝 (∫ z, ψ z*G.density z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))) := by
  let a : (ℝ × Position) × Velocity → ℝ := fun p => ψ (p.1.1,(p.1.2,p.2))/(1+‖p.2‖)
  have ham : Measurable a := (hψ.comp
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).div
    (measurable_const.add measurable_snd.norm)
  have hab p : |a p| ≤ C := by
    rw [show a p = ψ (p.1.1,(p.1.2,p.2))/(1+‖p.2‖) from rfl,abs_div,
      abs_of_pos (by positivity : 0 < 1+‖p.2‖)]
    exact (div_le_iff₀ (by positivity : 0 < 1+‖p.2‖)).mpr (hC _)
  have he (u : ℝ × Phase → ℝ) :
      (∫ p, a p*linearMoment (fun p => u (p.1.1,(p.1.2,p.2))) p
        ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) =
      ∫ z, ψ z*u z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase) := by
    have hp p : a p*linearMoment (fun p => u (p.1.1,(p.1.2,p.2))) p =
        ψ (p.1.1,(p.1.2,p.2))*u (p.1.1,(p.1.2,p.2)) := by
      dsimp only [a,linearMoment]
      field_simp [show (1+‖p.2‖:ℝ) ≠ 0 by positivity]
    simp_rw [hp]
    exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding (fun z : ℝ × Phase => ψ z*u z)
  have h := (G.weak_linearMoment_on_window hf hi hT).2.2 a ham ⟨C,hab⟩
  change Tendsto (fun n => ∫ p, a p*linearMoment (fun p =>
    (approximatingSolution f hfm (G.indices n)).density (p.1.1,(p.1.2,p.2))) p
    ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) atTop
    (𝓝 (∫ p, a p*linearMoment (fun p => G.density (p.1.1,(p.1.2,p.2))) p
      ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume)) at h
  simpa only [he] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # One actual global density identifies the mass-normalized physical collision rates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem exists_globalWeakLimit_with_normalized_rates
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massNormalizedPreRate (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massNormalizedPostRate (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile) := by
  obtain ⟨G,hG⟩ := exists_globalWeakLimit_with_weighted_pairs f hfm hf hi
  refine ⟨G,fun T hT => ?_⟩
  have hw := hG T hT
  rw [← Measure.volume_eq_prod] at hw
  have hFi n : Integrable (Compactness.weightedNormalizedPair
      (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
        (volume : Measure (Velocity × Velocity))) := by
    rw [Measure.volume_eq_prod]
    exact Compactness.weightedNormalizedPair_integrable
      (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
      (fun _ => (approximatingSolution f hfm (G.indices n)).nonnegative _)
      ((approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
        (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
  exact ⟨weak_massNormalizedPreRate hw hFi,
    weak_massNormalizedPostRate (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
      G.kineticProfile_measurable hw hFi⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Retaining strong spatial masses and both finite collision rates in one global limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalWeakLimit.finite_rates_of_pairs
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T)
    (hp : Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume
        (approximatingSolution f hfm (G.indices n)).kineticProfile)
      (Compactness.normalizedPair volume G.kineticProfile)) :
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile) := by
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.indices n)).kineticProfile
  have hFm n : Measurable (F n) := (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
  have hF n p : 0 ≤ F n p := (approximatingSolution f hfm (G.indices n)).nonnegative _
  have hFi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f :=
    (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hN n : 0 < (G.indices n:ℝ)+1 := by positivity
  have hNt : Tendsto (fun n => (G.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  obtain ⟨B,hB⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1.2
  have hFB n : eLpNorm (F n) 1 (μ.prod volume) ≤ B := hB (G.indices n)
  have hw := G.weightedPair_on_window hf hi hT hp
  rw [← Measure.volume_eq_prod] at hw
  have hwi n : Integrable (Compactness.weightedNormalizedPair (F n))
      (μ.prod (volume : Measure (Velocity × Velocity))) := by
    rw [Measure.volume_eq_prod]
    exact Compactness.weightedNormalizedPair_integrable (hFm n) (hF n) (hFi n)
  have hpre := weak_massNormalizedPreRate hw hwi
  have hpost := weak_massNormalizedPostRate hFm G.kineticProfile_measurable hw hwi
  exact ⟨weak_massRegularizedPreRate hFm hF hFi hFb hN hNt B hFB hpre,
    weak_massRegularizedPostRate hFm hF hFi hFb hN hNt B hFB hpost⟩


theorem exists_globalWeakLimit_with_strong_mass_rates
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm,
      (∀ T : ℝ, 0 ≤ T → Tendsto (fun n => eLpNorm (fun z =>
        Compactness.fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile z-
        Compactness.fiberMass volume G.kineticProfile z)
        1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0)) ∧
      (∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile)) := by
  obtain ⟨G,hm,hp⟩ := exists_globalWeakLimit_with_strong_mass_pairs f hfm hf hi
  exact ⟨G,hm,fun T hT => G.finite_rates_of_pairs hf hi hT (hp T hT)⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Full physical dissipation of the actual global periodic weak limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

theorem GlobalWeakLimit.physical_dissipation_le_liminf
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (_hT : 0 ≤ T)
    (hm : Tendsto (fun n => eLpNorm (fun x =>
      fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile x-
      fiberMass volume G.kineticProfile x) 1
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0))
    (hc :       Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile)) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.kineticProfile ≤
      liminf (fun n => extendedDissipation
        ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) ((G.indices n:ℝ)+1)
        (approximatingSolution f hfm (G.indices n)).kineticProfile) atTop := by
  exact full_dissipation_le_liminf
    (fun n => (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable)
    G.kineticProfile_measurable
    (fun n _ => (approximatingSolution f hfm (G.indices n)).nonnegative _)
    (fun _ => G.nonnegative _)
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
    (fun n => (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _))
    (fun _ => by positivity) hm hc.1 hc.2

theorem GlobalWeakLimit.physical_dissipation_bound
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T)
    (hm : Tendsto (fun n => eLpNorm (fun x =>
      fiberMass volume (approximatingSolution f hfm (G.indices n)).kineticProfile x-
      fiberMass volume G.kineticProfile x) 1
      ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0))
    (hc :       Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile)) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.kineticProfile ≤
      ENNReal.ofReal (initialEntropyBudget f) := by
  have hN : Tendsto (fun n => (G.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  apply (G.physical_dissipation_le_liminf hf hi hT hm hc).trans
  exact liminf_le_of_frequently_le ((hN.eventually (eventually_ge_atTop T)).mono (fun n hn =>
    approximatingSolution_dissipation_bound f hfm hf hi hT hn)).frequently

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The actual global approximation sequence has physical collision-rate weak limits -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem exists_globalWeakLimit_with_finite_rates
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    ∃ G : GlobalWeakLimit f hfm, ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPreRate G.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((G.indices n:ℝ)+1)
          (approximatingSolution f hfm (G.indices n)).kineticProfile)
        (massNormalizedPostRate G.kineticProfile) := by
  obtain ⟨G,hG⟩ := exists_globalWeakLimit_with_normalized_rates f hfm hf hi
  refine ⟨G,fun T hT => ?_⟩
  let μ : Measure (ℝ × Position) := (volume.restrict (Icc 0 T)).prod volume
  let F n := (approximatingSolution f hfm (G.indices n)).kineticProfile
  have hFm n : Measurable (F n) := (approximatingSolution f hfm (G.indices n)).kineticProfile_measurable
  have hF n p : 0 ≤ F n p := (approximatingSolution f hfm (G.indices n)).nonnegative _
  have hFi n : Integrable (entropyGauge (F n)) (μ.prod volume) :=
    (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integrable
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hFb n : (∫ p, entropyGauge (F n) p ∂μ.prod volume) ≤
      (volume.restrict (Icc 0 T)).real univ*approximationEntropyBudget f :=
    (approximatingSolution f hfm (G.indices n)).kinetic_entropy_integral_le
      (μ := volume.restrict (Icc 0 T)) (by positivity) (approximatingSolution_entropy f hfm hf hi _)
  have hN n : 0 < (G.indices n:ℝ)+1 := by positivity
  have hNt : Tendsto (fun n => (G.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  obtain ⟨B,hB⟩ := (approximatingSolution_compactness_hypotheses f hfm hf hi
    (volume.restrict (Icc 0 T))).1.2
  have hFB n : eLpNorm (F n) 1 (μ.prod volume) ≤ B := hB (G.indices n)
  exact ⟨weak_massRegularizedPreRate hFm hF hFi hFb hN hNt B hFB (hG T hT).1,
    weak_massRegularizedPostRate hFm hF hFi hFb hN hNt B hFB (hG T hT).2⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local mass transport tests pass through the actual density limit -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.mass_transport_tendsto {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (φ : MassTest) :
    Tendsto (fun n => ∫ z, (approximatingSolution f hfm (G.indices n)).density z*
      φ.transportDerivative z.1 z.2 ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) atTop
      (𝓝 (∫ z, G.density z*φ.transportDerivative z.1 z.2
        ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))) := by
  let ψ : ℝ × Phase → ℝ := fun z => if z.1 ∈ Icc 0 T then φ.transportDerivative z.1 z.2 else 0
  have hm : Measurable ψ := φ.measurable_transportDerivative.ite
    (measurableSet_Icc.preimage measurable_fst) measurable_const
  obtain ⟨C,hC,hb⟩ := φ.bounded_on_time T
  have hψ z : |ψ z| ≤ C*(1+‖z.2.2‖) := by
    dsimp only [ψ]
    split_ifs with ht
    · exact (hb z.1 ht z.2).2
    · simp only [abs_zero]
      positivity
  have he (u : ℝ × Phase → ℝ) :
      (∫ z, ψ z*u z ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase)) =
      ∫ z, u z*φ.transportDerivative z.1 z.2
        ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase) := by
    apply integral_congr_ae
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with z ht
    rw [show ψ z = φ.transportDerivative z.1 z.2 from ite_eq_left ht]
    exact mul_comm _ _
  have h := G.linear_test_tendsto hf hi hT hm C hψ
  simpa only [he] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Local mass balance of every actual supported approximation -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem BoundedCutoffSolution.local_mass_balance {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) {R : ℝ} (hR : R ∈ Icc 0 T)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (fun p => S.density (z.1,p)) z.2)
      ((volume.restrict (Icc 0 R)).prod volume)) (φ : MassTest) :
    (∫ z, S.density z*φ.transportDerivative z.1 z.2
      ∂(volume.restrict (Icc 0 R)).prod (volume : Measure Phase)) =
      (∫ p : Phase, S.density (R,p)*φ.toFun R p.1)-
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 R)
  let I : ℝ × Phase → ℝ := fun z => S.density z*φ.transportDerivative z.1 z.2+
    S.collision z*φ.toFun z.1 z.2.1
  let B : Phase → ℝ := fun p => S.density (R,p)*φ.toFun R p.1
  let B₀ : Phase → ℝ := fun p => f₀ p*φ.toFun 0 p.1
  have htr := mass_transport_integrable S.measurable (fun t p => S.nonnegative (t,p)) hEi φ
  have hsrc := S.mass_source_zero hN R φ
  have hIi : Integrable I (μ.prod volume) := htr.add hsrc.1
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hf (t : ℝ) : Integrable (fun p => S.density (t,p)) := by
    simpa only [one_mul] using S.weighted_density_integrable hN.le (fun _ => 1)
      measurable_const (fun _ _ => by norm_num : ∀ v : Velocity, ‖v‖ ≤ N → |(1:ℝ)| ≤ 1) t
  have hBi : Integrable B := φ.slice_integrable ⟨hR.1,le_rfl⟩ (hf R)
  have hB₀i : Integrable B₀ := φ.slice_integrable ⟨le_rfl,hR.1⟩
    (S.initial_integrable hN.le (hR.1.trans hR.2))
  have hp (p : Phase) : (∫ t, TorusFlight.along I (t,p) ∂μ) =
      B (TorusFlight.flight R p)-B₀ p := by
    have h := S.mass_tested_path hN hR φ p
    rw [intervalIntegral.integral_of_le hR.1,← integral_Icc_eq_integral_Ioc] at h
    exact h
  have he : (∫ z, I z ∂μ.prod volume) = (∫ p, B p)-(∫ p, B₀ p) := by
    calc
      _ = ∫ z, TorusFlight.along I z ∂μ.prod volume := (TorusFlight.integral_along hIi).symm
      _ = ∫ p : Phase, ∫ t, TorusFlight.along I (t,p) ∂μ := integral_prod_symm _ hAi
      _ = ∫ p : Phase, B (TorusFlight.flight R p)-B₀ p := integral_congr_ae (ae_of_all _ hp)
      _ = (∫ p : Phase, B (TorusFlight.flight R p))-(∫ p : Phase, B₀ p) :=
        integral_sub ((TorusFlight.flight_measurePreserving R).integrable_comp_of_integrable hBi) hB₀i
      _ = _ := by rw [TorusFlight.integral_flight]
  change (∫ z, S.density z*φ.transportDerivative z.1 z.2+
    S.collision z*φ.toFun z.1 z.2.1 ∂μ.prod volume) = _ at he
  rw [integral_add htr hsrc.1,hsrc.2,add_zero] at he
  exact he

theorem BoundedCutoffSolution.local_mass_equation {N T : ℝ} {f₀ : Density}
    (S : BoundedCutoffSolution N T f₀) (hN : 0 < N) {R : ℝ} (hR : R ∈ Icc 0 T)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (fun p => S.density (z.1,p)) z.2)
      ((volume.restrict (Icc 0 R)).prod volume)) (φ : MassTest)
    (hφ : ∀ x, φ.toFun R x = 0) :
    (∫ z, S.density z*φ.transportDerivative z.1 z.2
      ∂(volume.restrict (Icc 0 R)).prod (volume : Measure Phase))+
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) = 0 := by
  rw [S.local_mass_balance hN hR hEi φ]
  simp only [hφ,mul_zero,integral_zero,zero_sub,neg_add_cancel]

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The same global weak density satisfies the local mass equation -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem GlobalWeakLimit.local_mass_equation {f : Density} {hfm : Measurable f}
    (G : GlobalWeakLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) (φ : MassTest) (hφ : ∀ x, φ.toFun T x = 0) :
    (∫ z, G.density z*φ.transportDerivative z.1 z.2
      ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
      (∫ p : Phase, f p*φ.toFun 0 p.1) = 0 := by
  let S n := approximatingSolution f hfm (G.indices n)
  have hEi n : Integrable (fun z : ℝ × Phase =>
      entropyMoment (fun p => (S n).density (z.1,p)) z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
    have h := (S n).kinetic_entropy_integrable (μ := volume.restrict (Icc 0 T))
      (by positivity) (approximatingSolution_entropy f hfm hf hi _)
    exact (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable h
  have ht : Tendsto (fun n => (G.indices n : ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  have he : ∀ᶠ n in atTop,
      (∫ z, (S n).density z*φ.transportDerivative z.1 z.2
        ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
        (∫ p : Phase, initialApproximation ((G.indices n:ℝ)+1) f p*φ.toFun 0 p.1) = 0 := by
    filter_upwards [ht.eventually (eventually_ge_atTop T)] with n hn
    exact (S n).local_mass_equation (by positivity) ⟨hT,hn⟩ (hEi n) φ hφ
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  have htest : Measurable (fun p : Phase => φ.toFun 0 p.1) :=
    φ.measurable_toFun.comp (measurable_const.prodMk measurable_id)
  have hinit := (initialApproximation_test_tendsto hfm hf
    (show FiniteEntropyDatum f from ⟨ae_of_all _ hf,hfm.aestronglyMeasurable,hi⟩).integrable
    htest C (fun p => (hb 0 ⟨le_rfl,hT⟩ p).1)).comp G.increasing.tendsto_atTop
  simp_rw [mul_comm (φ.toFun 0 _) _] at hinit
  have hlim := (G.mass_transport_tendsto hf hi hT φ).add hinit
  have hzero : Tendsto (fun n =>
      (∫ z, (S n).density z*φ.transportDerivative z.1 z.2
        ∂(volume.restrict (Icc 0 T)).prod (volume : Measure Phase))+
        (∫ p : Phase, initialApproximation ((G.indices n:ℝ)+1) f p*φ.toFun 0 p.1))
      atTop (𝓝 0) := tendsto_const_nhds.congr' (he.mono (fun _ hn => hn.symm))
  exact tendsto_nhds_unique hlim hzero

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Actual collision fibers and renormalized gain/loss of the global weak density -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

theorem GlobalWeakLimit.normalized_collision_integrability
    {f : Density} {hfm : Measurable f} (G : GlobalWeakLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T)
    (hD : rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))
      G.kineticProfile < ⊤) :
    Integrable (fun p => gainDensity G.kineticProfile p/(1+G.kineticProfile p/maxwellian p.2))
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) ∧
    Integrable (fun p => lossDensity G.kineticProfile p/(1+G.kineticProfile p/maxwellian p.2))
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) ∧
    ∀ᵐ p ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume : Measure Velocity),
      Integrable (fun q => postRate G.kineticProfile (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q => preRate G.kineticProfile (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) := by
  have hE := G.kinetic_entropy_on_window hf hi hT
  have hn p : 0 ≤ G.kineticProfile p := G.nonnegative _
  have hI := integrable_of_entropyGauge G.kineticProfile_measurable hn hE
  apply normalized_gainLoss_and_fibers G.kineticProfile_measurable hn hI _ hD
  have hL := linearMoment_integrable G.kineticProfile_measurable hn hE
  convert hL.sub hI using 1
  funext p
  simp only [linearMoment,Pi.sub_apply]
  ring

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # A single global collision limit retains its strong masses and physical rates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness

structure GlobalCollisionLimit (f : Density) (hfm : Measurable f) where
  weakLimit : GlobalWeakLimit f hfm
  mass_strong : ∀ T : ℝ, 0 ≤ T → Tendsto (fun n => eLpNorm (fun z =>
        Compactness.fiberMass volume (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile z-
        Compactness.fiberMass volume weakLimit.kineticProfile z)
        1 ((volume.restrict (Icc 0 T)).prod (volume : Measure Position))) atTop (𝓝 0)
  normalized_pairs : ∀ T : ℝ, 0 ≤ T → Published.WeakL1Converges
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume.prod volume))
      (fun n => Compactness.normalizedPair volume
        (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
      (Compactness.normalizedPair volume weakLimit.kineticProfile)
  finite_rates : ∀ T : ℝ, 0 ≤ T →
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPreRate ((weakLimit.indices n:ℝ)+1)
          (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
        (massNormalizedPreRate weakLimit.kineticProfile) ∧
      Published.WeakL1Converges
        ((((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod
          (volume : Measure (Velocity × Velocity))).prod sphereArea)
        (fun n => massRegularizedPostRate ((weakLimit.indices n:ℝ)+1)
          (approximatingSolution f hfm (weakLimit.indices n)).kineticProfile)
        (massNormalizedPostRate weakLimit.kineticProfile)

theorem exists_globalCollisionLimit
    (f : Density) (hfm : Measurable f) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) :
    Nonempty (GlobalCollisionLimit f hfm) := by
  obtain ⟨G,hm,hp⟩ := exists_globalWeakLimit_with_strong_mass_pairs f hfm hf hi
  exact ⟨⟨G,hm,hp,fun T hT => G.finite_rates_of_pairs hf hi hT (hp T hT)⟩⟩

theorem GlobalCollisionLimit.dissipation_bound {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    rateDissipation ((volume.restrict (Icc 0 T)).prod (volume : Measure Position)) G.weakLimit.kineticProfile ≤
      ENNReal.ofReal (initialEntropyBudget f) :=
  G.weakLimit.physical_dissipation_bound hf hi hT (G.mass_strong T hT) (G.finite_rates T hT)

theorem GlobalCollisionLimit.normalized_integrability {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p => gainDensity G.weakLimit.kineticProfile p/
      (1+G.weakLimit.kineticProfile p/maxwellian p.2))
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) ∧
    Integrable (fun p => lossDensity G.weakLimit.kineticProfile p/
      (1+G.weakLimit.kineticProfile p/maxwellian p.2))
      (((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod volume) ∧
    ∀ᵐ p ∂((volume.restrict (Icc 0 T)).prod (volume : Measure Position)).prod (volume : Measure Velocity),
      Integrable (fun q => postRate G.weakLimit.kineticProfile (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q => preRate G.weakLimit.kineticProfile (collisionGrouping.symm (p,q)))
        ((volume : Measure Velocity).prod sphereArea) :=
  G.weakLimit.normalized_collision_integrability hf hi hT
    ((G.dissipation_bound hf hi hT).trans_lt ENNReal.ofReal_lt_top)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # The sharp joint budget passes to the actual global limit on every time set -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

theorem GlobalCollisionLimit.averaged_joint_budget {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) {S : Set ℝ}
    (hS : MeasurableSet S) (hSR : S ⊆ Icc r R) :
    (∫⁻ t in S, entropyMarginal G.weakLimit.density t)+
      volume S*rateDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
        G.weakLimit.kineticProfile ≤ volume S*ENNReal.ofReal (relativeEntropy f) := by
  let μ : Measure ℝ := volume.restrict S
  let F n := (approximatingSolution f hfm (G.weakLimit.indices n)).density
  let D n := extendedDissipation ((volume.restrict (Icc 0 r)).prod (volume : Measure Position))
    ((G.weakLimit.indices n:ℝ)+1) (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile
  let C n := ENNReal.ofReal (relativeEntropy (initialApproximation ((G.weakLimit.indices n:ℝ)+1) f))
  have hR : 0 ≤ R := hr.trans hrR
  have hS0 : S ⊆ Icc 0 R := hSR.trans (Icc_subset_Icc hr le_rfl)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    ((measure_mono hSR).trans_lt isCompact_Icc.measure_lt_top).ne
  have hw := (G.weakLimit.weak_on_window hR).restrict_base hS
  rw [Measure.restrict_restrict hS,inter_eq_left.mpr hS0] at hw
  have hFm n : Measurable (F n) := (approximatingSolution f hfm (G.weakLimit.indices n)).measurable
  have hFi n : Integrable (F n) (μ.prod volume) :=
    density_integrable_of_spacetimeEntropy (hFm n)
      (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative
      (approximatingSolution_spacetimeEntropy_integrable f hfm hf hi _ μ)
  have hh := entropyMarginal_liminf hw hFm hFi
    (fun n => (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative) G.weakLimit.nonnegative
  have hd := G.weakLimit.physical_dissipation_le_liminf hf hi hr
    (G.mass_strong r hr) (G.finite_rates r hr)
  have hC : Tendsto C atTop (𝓝 (ENNReal.ofReal (relativeEntropy f))) :=
    ENNReal.tendsto_ofReal ((initialApproximation_relativeEntropy_tendsto hfm hf hi).comp
      G.weakLimit.increasing.tendsto_atTop)
  have hN : Tendsto (fun n => (G.weakLimit.indices n:ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp G.weakLimit.increasing.tendsto_atTop).atTop_add tendsto_const_nhds
  have hu : ∀ᶠ n in atTop, ∀ᵐ t ∂μ, entropyMarginal (F n) t+D n ≤ C n := by
    filter_upwards [hN.eventually (eventually_ge_atTop R)] with n hn
    filter_upwards [ae_restrict_mem hS] with t ht
    have hnt : t ≤ (G.weakLimit.indices n:ℝ)+1 := (hSR ht).2.trans hn
    rw [entropyMarginal_eq (hFm n)
      (approximatingSolution f hfm (G.weakLimit.indices n)).nonnegative t
      ((approximatingSolution f hfm (G.weakLimit.indices n)).finiteEntropy (by positivity) t).2.2]
    exact (approximatingSolution f hfm (G.weakLimit.indices n)).earlier_joint_budget
      (by positivity) (by positivity) hr (hSR ht).1 hnt
  have h := entropy_dissipation_average_limit
    (μ := μ) (fun n => entropyMarginal_measurable (hFm n)) hh hd hC hu
  simpa only [μ,Measure.restrict_apply_univ] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
