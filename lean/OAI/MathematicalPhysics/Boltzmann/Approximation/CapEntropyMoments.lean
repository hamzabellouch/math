import OAI.MathematicalPhysics.Boltzmann.Approximation.CapDilationScales
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMildLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildConservation
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalizedBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.Moments
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteDepthKernelOrder
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteRatesWindowUI
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # The actual cap shots satisfy the finite entropy-dissipation inequality -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem CapApproximation.entropy_dissipation
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ENNReal.ofReal (relativeEntropy (F.solution.torusEvolution t))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume t) (N+1)
        (torusPhysical q F.solution.value) ≤
      ENNReal.ofReal (relativeEntropy (periodicInitial s₀ η K α γ d₀ q N F.coefficient)) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh : ∀ p, 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds hδ hδmax q
    intro p
    exact mul_nonneg F.coefficient_mem.1 (hb p).1
  have hn (p) : 0 ≤ initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p := by
    simpa using (initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh).2 ∅ p
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := F.solution.entropy_dissipation_inequality hcarleman hq₁ hq₂ (by positivity)
    (show 0 ≤ 2*F.amplitude from mul_nonneg (by norm_num) F.amplitude_pos.le) ht htT le_rfl hm
    (fun p => ⟨hn p,F.initial_bound p⟩)
  have he : TorusFlight.initialDensity q (initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) =
      periodicInitial s₀ η K α γ d₀ q N F.coefficient := by
    funext p
    exact mul_comm _ _
  rw [he] at h
  exact h

theorem CapApproximation.finiteEntropy
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) (t : ℝ) :
    FiniteEntropyDatum (F.solution.torusEvolution t) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  apply bounded_finiteEntropyDatum (A := 2*F.amplitude) hq₂ (mul_nonneg (by norm_num) F.amplitude_pos.le) hp hpi
  · exact (torusPhysical_measurable F.solution.measurable_value q).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  · exact fun z => torusPhysical_nonneg (fun u => (F.solution.value_bounds u).1) q _
  · intro z
    exact (mul_le_mul_of_nonneg_left (F.solution.value_bounds
      (t,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2
      (H_nonneg q z.2)).trans_eq (mul_comm _ _)

theorem CapApproximation.entropy_dissipation_extended
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : CapApproximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z)))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume t) (N+1)
        (torusPhysical q F.solution.value) ≤
      ENNReal.ofReal (relativeEntropy (periodicInitial s₀ η K α γ d₀ q N F.coefficient)) := by
  have hi := F.finiteEntropy hq₁ hq₂ t
  have hsi : Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z)) :=
    (FiniteEntropyDatum.integrable_relativeEntropy hi).congr (ae_of_all _ (fun z =>
      (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have hn : ∀ z, 0 ≤ F.solution.torusEvolution t z := fun z =>
    torusPhysical_nonneg (fun u => (F.solution.value_bounds u).1) q _
  have he : relativeEntropy (F.solution.torusEvolution t) =
      ∫ z, scalarRelativeEntropy (maxwellian z.2) (F.solution.torusEvolution t z) :=
    integral_congr_ae (ae_of_all _ (fun z => (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
  have h := F.entropy_dissipation hcarleman hs₀ hsmax hη hηmax hK hd₀ hq₁ hq₂ ht htT
  rw [he,ofReal_integral_eq_lintegral_ofReal hsi (ae_of_all _ (fun z =>
    scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hn z)))] at h
  exact h

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Every-time weak traces for the same cap subsequence as the nonlinear mild limit -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.weak_each_time
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hr : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value))
      (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p))
    {t : ℝ} (ht : t ∈ Icc 0 F.time) :
    Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  let r : ℕ → (ℝ × Position) × Velocity → ℝ := fun n =>
    CollisionCompactness.collisionSource (φ n+1) (torusPhysical q (F.approximation (φ n)).solution.value)
  let a : ℕ → Density := fun n => periodicInitial s₀ η K α γ d₀ q (φ n)
    (F.approximation (φ n)).coefficient
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hri n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactCapFamily.source_ui.memLp (φ n))
  have ha := (F.toCompactCapFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  exact S.weak_kinetic_trace F.time_pos hfm hrm hri ha hai hr t ht
    (fun n => (F.approximation (φ n)).characteristic_slice hcarleman hq₁ hq₂ ht)

theorem TightCapFamily.exists_mild_limit_with_traces_and_convergence
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
      ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
        (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
        (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,hr⟩ := F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,hg,S,hpair,fun _ ht => F.weak_each_time hcarleman
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂ hφ S hr ht⟩

theorem TightCapFamily.exists_mild_limit_with_time_traces
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
        (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
        (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  obtain ⟨φ,g,hφ,_hg,S,hpair,hr⟩ := F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,S,hpair,fun _ ht => F.weak_each_time hcarleman
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂ hφ S hr ht⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Entropy and dissipation for the actual cap limit at every positive local time -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.entropy_mild_limit_of_convergence
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hpair : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.pairDensity
        (torusPhysical q (F.approximation (φ n)).solution.value)) (CollisionCompactness.pairDensity g))
    (htrace : ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) :
    ∀ t ∈ Ioc 0 F.time,
        (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2)
          (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀)) := by
  intro t ht
  let f : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => torusPhysical q (F.approximation (φ n)).solution.value
  have hfm n : Measurable (f n) :=
    torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n p : 0 ≤ f n p := torusPhysical_nonneg
    (fun u => ((F.approximation (φ n)).solution.value_bounds u).1) q p
  have hfi n := FiniteEntropyDatum.integrable ((F.approximation (φ n)).finiteEntropy hq₁ hq₂ t)
  have hH := (htrace t ⟨ht.1.le,ht.2⟩).entropy_liminf hfi
    (fun n => ae_of_all _ (fun z => hfn n ((t,z.1),z.2)))
    (ae_of_all _ (fun z => MildCollisionSolution.positiveEvolution_nonnegative t z))
    (by unfold maxwellian; fun_prop) integrable_maxwellian_phase
    (ae_of_all _ (fun z => maxwellian_pos z.2))
  have hpairt := hpair.restrict_time ht.2
  have hpint n : Integrable (CollisionCompactness.pairDensity (f n))
      ((AnnularEnvelope.timePositionVolume t).prod volume) :=
    (memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))).mono_measure
      (Measure.prod_mono (timePositionVolume_mono ht.2) le_rfl)
  have hb : Tendsto (fun n => (φ n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n, (φ n:ℝ) ≤ (φ n:ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hD := CollisionCompactness.rateDissipation_le_liminf_cutoff hfm hfn S.measurable
    S.nonnegative hpairt hpint hb
  have hC := (periodicInitial_entropy_tendsto hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax hq₁ hq₂
    (fun n => (F.approximation n).coefficient_mem)).comp hφ.tendsto_atTop
  exact entropy_dissipation_of_liminfs hH hD hC (Eventually.of_forall (fun n =>
    (F.approximation (φ n)).entropy_dissipation_extended hcarleman hs₀ hsmax hη hηmax
      hK.le hd₀.le hq₁ hq₂ ht.1 ht.2))

theorem TightCapFamily.exists_entropy_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ g : (ℝ × Position) × Velocity → ℝ,
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      ∀ t ∈ Ioc 0 F.time,
        (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2)
          (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀)) := by
  obtain ⟨φ,g,hφ,S,hpair,htrace⟩ := F.exists_mild_limit_with_time_traces hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  exact ⟨g,S,F.entropy_mild_limit_of_convergence hcarleman hs₀ hsmax hη hηmax hK hγ hd₀
    hwidth hα hαmax hq₁ hq₂ hφ S hpair htrace⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The constructed cold-datum solution conserves energy at every local time -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_energy_conserving_local_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ F : Evolution, LocalMildSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) F ∧
      (∀ t ∈ Icc 0 A.time, (∫ p, F t p) = ∫ p, JetPeriodicDatum.datum s₀ η K α γ d₀ p) ∧
      (∀ t ∈ Icc 0 A.time, energy (F t) = energy (JetPeriodicDatum.datum s₀ η K α γ d₀)) := by
  obtain ⟨φ,g,_hφ,hg,S⟩ := A.exists_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hi := FiniteEntropyDatum.integrable hdatum
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  have hbound := A.toCompactCapFamily.weak_limit_moment hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  refine ⟨MildCollisionSolution.positiveEvolution A.time _ g,
    S.localMildSolution A.time_pos hm hi hn,?_,?_⟩
  · exact fun t ht => S.mass_conservation A.time_pos hm hi ht
  · exact fun t ht => S.energy_conservation A.time_pos hm hi (FiniteEntropyDatum.integrable_energy hdatum) hE ht

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # The local solution satisfies the manuscript's every-time entropy inequality -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_finite_entropy_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hγ : 0 < γ) (hd₀ : 0 < d₀)
    (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64) (hα : 0 ≤ α) (hαmax : α ≤ 1/4)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ g : (ℝ × Position) × Velocity → ℝ,
      MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      (∀ t ∈ Icc 0 A.time, FiniteEntropyDatum
        (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) ∧
      (∀ t ∈ Icc 0 A.time,
        ENNReal.ofReal (relativeEntropy
          (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t))+
        (∫⁻ s in Icc (0:ℝ) t, entropyDissipation
          (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g s)) ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))) := by
  obtain ⟨g,S,hH⟩ := A.exists_entropy_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax hq₁ hq₂
  let f₀ := JetPeriodicDatum.datum s₀ η K α γ d₀
  have hf₀ : FiniteEntropyDatum f₀ :=
    JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα hαmax
  have hm₀ : Measurable f₀ := JetPeriodicDatum.measurable_pullback
    (Measurable.tsum (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn₀ : ∀ z, 0 ≤ f₀ z := fun z =>
    JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  exact ⟨g,S,S.entropy_admissible A.time_pos hf₀ hm₀ hn₀ hH⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Entropy and exponential pair control for the same actual cap limit -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem TightCapFamily.exists_entropy_moment_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightCapFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ g : (ℝ × Position) × Velocity → ℝ,
      MildCollisionSolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      (∀ t ∈ Icc 0 A.time, FiniteEntropyDatum
        (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t)) ∧
      (∀ t ∈ Icc 0 A.time,
        ENNReal.ofReal (relativeEntropy
          (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t))+
        (∫⁻ s in Icc (0:ℝ) t, entropyDissipation
          (MildCollisionSolution.positiveEvolution A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g s)) ≤
          ENNReal.ofReal (relativeEntropy (JetPeriodicDatum.datum s₀ η K α γ d₀))) ∧
      Integrable (CollisionCompactness.exponentialPair g)
        ((AnnularEnvelope.timePositionVolume A.time).prod volume) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,htrace⟩ := A.exists_mild_limit_with_traces_and_convergence
    hcarleman hGLPS hDP hs₀ hsmax hη hηmax hK.le hγ hd₀ hq₁ hq₂
  have hH := A.entropy_mild_limit_of_convergence hcarleman hs₀ hsmax hη hηmax hK hγ hd₀
    hwidth hα.le hαmax hq₁ hq₂ hφ S hpair htrace
  have hdatum := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  obtain ⟨hfinite,hentropy⟩ := S.entropy_admissible A.time_pos hdatum hm hn hH
  have hbound := A.toCompactCapFamily.weak_limit_moment hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  exact ⟨g,S,hfinite,hentropy,hE⟩

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
