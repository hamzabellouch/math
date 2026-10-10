import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionDissipation
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMassClip
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakDuhamelLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # Convergence of the actual right-hand sides of the cap equations -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_cutoff_equation_limit_with_pair
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_positive_nonlinear_limit hcarleman hGLPS hDP hq₁ hq₂
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n := torusPhysical_nonneg
    (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q
  have hf n := memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))
  have hb : Tendsto (fun n => (φ n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n, (φ n : ℝ) ≤ (φ n : ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hterms := CollisionCompactness.weak_cutoff_gainLoss hfm hfn hg.1 hpair hf hb
  have hdiff := hterms.1.sub hterms.2
    (fun n => memLp_one_iff_integrable.mp (F.gain_ui.memLp (φ n)))
    (fun n => memLp_one_iff_integrable.mp (F.loss_ui.memLp (φ n)))
  have he n : (fun p => KineticCollisionNullSets.gain (φ n+1)
      (torusPhysical q (F.approximation (φ n)).solution.value) p-
      CollisionCompactness.cutoffLossDensity (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) p) =ᵐ[
        (AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) := by
    filter_upwards [CollisionCompactness.cutoff_loss_ae_eq_frequency (hfm n) (hfn n) (hf n)
      (φ n+1)] with p hp
    simp only [CollisionCompactness.collisionSource,hp]
  exact ⟨φ,g,hφ,hg,hdiff.congr_sequence he,hpair.2.1,hgn,hpair⟩

theorem TightCapFamily.exists_cutoff_equation_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hr,hpi,hgn,_hpair⟩ :=
    F.exists_cutoff_equation_limit_with_pair hcarleman hGLPS hDP hq₁ hq₂
  exact ⟨φ,g,hφ,hg,hr,hpi,hgn⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The cap approximations satisfy the actual torus initial-value identity -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_measurable (s₀ η K α γ d₀ q : ℝ) (N : ℕ) (ell : ℝ) :
    Measurable (periodicInitial s₀ η K α γ d₀ q N ell) := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul ell)
  have he : periodicInitial s₀ η K α γ d₀ q N ell =
      TorusFlight.initialDensity q (initial s₀ η K α γ d₀ q N
        (fun p => ell*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) := by
    funext p
    exact mul_comm _ _
  rw [he]
  exact TorusFlight.initialDensity_measurable hm q

theorem CapApproximation.spacetime_mild (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) :
    TorusFlight.along (TorusFlight.regroup (torusPhysical q F.solution.value)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => periodicInitial s₀ η K α γ d₀ q N F.coefficient z.2 +
      Published.timePrimitive (volume.restrict (Icc 0 T))
        (TorusFlight.along (TorusFlight.regroup
          (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) z) := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.spacetime_mild hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) hT le_rfl le_rfl hm
  filter_upwards [h] with z hz
  convert hz using 1
  congr 1
  exact mul_comm _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every-time characteristic traces of the finite cap approximations -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.characteristic_slice (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun p => torusPhysical q F.solution.value
      ((t,(TorusFlight.flight t p).1),(TorusFlight.flight t p).2)) =ᵐ[volume]
    TorusFlight.characteristicProfile (volume.restrict (Icc 0 T))
      (periodicInitial s₀ η K α γ d₀ q N F.coefficient)
      (TorusFlight.along (TorusFlight.regroup
        (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) t := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.characteristic hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) ht.1 ht.2 le_rfl hm
  filter_upwards [h] with p hp
  change _ = periodicInitial s₀ η K α γ d₀ q N F.coefficient p+
    Published.timePrimitive (volume.restrict (Icc 0 T)) _ (t,p)
  rw [Published.timePrimitive_eq_interval ht]
  convert hp using 1
  congr 1
  exact mul_comm _ _

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The actual cap initial data converge weakly to the prescribed cold datum -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem periodicInitial_integrable {s₀ η K γ d₀ q : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2)
    (α : ℝ) (N : ℕ) (ell : ℝ) :
    Integrable (periodicInitial s₀ η K α γ d₀ q N ell) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have he : periodicInitial s₀ η K α γ d₀ q N ell =
      fun p => JetPeriodicDatum.truncated s₀ η K α γ d₀ N p+
        ell*HotSeedProfile.periodicDensity q (DatumBounds.scale s₀ η (N+1)) p :=
    funext (periodicInitial_eq hs₀ hsmax hη hηmax K α γ d₀ q N ell)
  rw [he]
  exact (JetPeriodicDatum.truncated_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α N).add
    ((HotSeedProfile.periodicDensity_integrable hq hqmax hδ hδmax).const_mul ell)

theorem CompactCapFamily.initial_weak_limit {s₀ η K α γ d₀ q : ℝ}
    (F : CompactCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2) :
    Published.WeakL1Converges volume
      (fun n => periodicInitial s₀ η K α γ d₀ q n (F.approximation n).coefficient)
      (JetPeriodicDatum.datum s₀ η K α γ d₀) := by
  have hi := JetPeriodicDatum.integrable_pullback
    (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  exact Published.weakL1_of_integral_norm_sub
    (fun n => periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hq hqmax α n _)
    (JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))) hi F.initial_l1

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # A genuine local mild solution obtained from the actual positive cap family -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

/-- The characteristic identity uses the full physical collision terms and the
prescribed initial density. The spacetime identity determines a continuous-time
representative through the Bochner integral of the collision source. -/
structure MildCollisionSolution (T : ℝ) (f₀ : Density)
    (g : (ℝ × Position) × Velocity → ℝ) : Prop where
  measurable : Measurable g
  nonnegative : ∀ z, 0 ≤ g z
  integrable : Integrable g ((AnnularEnvelope.timePositionVolume T).prod volume)
  pair_integrable : Integrable (CollisionCompactness.pairDensity g)
    ((AnnularEnvelope.timePositionVolume T).prod volume)
  characteristic : TorusFlight.along (TorusFlight.regroup g) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2+Published.timePrimitive (volume.restrict (Icc 0 T))
      (TorusFlight.along (TorusFlight.regroup
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p))) z)

namespace JetCopyDatum

theorem TightCapFamily.exists_mild_limit_with_convergence
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) := by
  obtain ⟨φ,g,hφ,hg,hr,hpair,hgn,hpairweak⟩ := F.exists_cutoff_equation_limit_with_pair hcarleman hGLPS hDP hq₁ hq₂
  let μ : Measure ℝ := volume.restrict (Icc 0 F.time)
  let f : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => torusPhysical q (F.approximation (φ n)).solution.value
  let r : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => CollisionCompactness.collisionSource (φ n+1) (f n)
  let a : ℕ → Phase → ℝ :=
    fun n => periodicInitial s₀ η K α γ d₀ q (φ n) (F.approximation (φ n)).coefficient
  have hfm n : Measurable (f n) :=
    torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hrint n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.source_ui.memLp (φ n))
  have hfr := TorusFlight.weak_regroup hfm hg
  have hrr := TorusFlight.weak_regroup hrm hr
  have hfa := TorusFlight.weak_along
    (fun n => (hfm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hfr
  have hra := TorusFlight.weak_along
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hrr
  have hrain n : Integrable (TorusFlight.along (TorusFlight.regroup (r n)))
      (μ.prod (volume : Measure Phase)) := by
    have hrreg : Integrable (TorusFlight.regroup (r n)) (μ.prod (volume : Measure Phase)) := by
      have hi := (measurePreserving_prodAssoc μ (volume : Measure Position)
        (volume : Measure Velocity)).symm.integrable_comp_of_integrable (hrint n)
      rw [Measure.volume_eq_prod]
      exact hi
    exact (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hrreg
  have ham n : Measurable (a n) := periodicInitial_measurable s₀ η K α γ d₀ q _ _
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  have ha := (F.toCompactCapFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have heq n : TorusFlight.along (TorusFlight.regroup (f n)) =ᵐ[μ.prod volume]
      (fun z => a n z.2+Published.timePrimitive μ
        (TorusFlight.along (TorusFlight.regroup (r n))) z) :=
    (F.approximation (φ n)).spacetime_mild hcarleman hq₁ hq₂ F.time_pos.le
  have hlim := TorusFlight.weak_duhamel_limit hfa hra
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable |>.comp
      (TorusFlight.along_measurePreserving μ).measurable)
    hrain ha ham hai heq
  exact ⟨φ,g,hφ,hg,⟨hg.1,hgn,hg.2.1,hpair,hlim⟩,hpairweak,hr⟩

theorem TightCapFamily.exists_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g := by
  obtain ⟨φ,g,hφ,hg,S,_hpair,_hr⟩ :=
    F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
      hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,hg,S⟩

end JetCopyDatum
end BoltzmannNonuniqueness

end

end

end OAI
