import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEntropyMoments
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapHotTransportBalance
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapLocalAdmissibility
import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapMildLimits

namespace OAI

section

/-! # Finite entropy-dissipation bounds for approximations below the cap -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.entropy_dissipation
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
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

theorem Approximation.finiteEntropy
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
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

theorem Approximation.entropy_dissipation_extended
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
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


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Every-time entropy and dissipation bounds for limits below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.entropy_mild_limit_of_convergence
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
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

theorem TightFamily.exists_entropy_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
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


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # The common half-Gaussian moment envelope for limits below the cap -/

noncomputable section
open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.moment_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T,
      VelocityMoment.moment (fun v => torusPhysical q F.solution.value (u,v)) ≤
        ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
          (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  have hδ : 0 < DatumBounds.scale s₀ η (N+1) := DatumBounds.scale_pos hs₀ _
  have hδmax : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hn p : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds hδ hδmax q
    exact mul_nonneg F.coefficient_mem.1 (hb p).1
  exact capped_spacetime_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
    hq (by positivity) (bounds (by positivity) F.amplitude_pos).1 hT
    (mul_nonneg (by norm_num) F.amplitude_pos.le) hTmax hδ hδmax le_rfl N
    ((HotSeedProfile.normalized_measurable q _).const_mul _) hn F.initial_bound F.solution F.cap_bound

theorem CompactFamily.weak_limit_moment {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ}
    (hg : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g)
    (hgn : ∀ p, 0 ≤ g p) :
    ∀ᵐ u ∂AnnularEnvelope.timePositionVolume F.time,
      VelocityMoment.moment (fun v => g (u,v)) ≤
        ENNReal.ofReal (AnnularEnvelope.commonMoment s₀ η
          (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)
          (AnnularEnvelope.torusChart u)) := by
  have hA := momentBase_nonneg hs₀ hK hd₀ η α q
  have hB := JetEnvelopeGain.momentConstant_nonneg hK α γ
  apply hg.velocity_moment
    (fun n => torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q)
    (fun n => torusPhysical_nonneg (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q)
    hgn (fun n => memLp_one_iff_integrable.mp (F.density_ui.memLp (φ n)))
    ((AnnularEnvelope.commonMoment_measurable s₀ η _ _).comp AnnularEnvelope.torusChart_measurable)
    (CollisionCompactness.torus_common_integrable hs₀ hη hηmax F.time_pos.le hA hB)
    (fun u => AnnularEnvelope.commonMoment_nonneg hA hB s₀ η (AnnularEnvelope.torusChart u))
  intro n
  exact (F.approximation (φ n)).moment_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq F.time_pos.le F.time_le


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Entropy and exponential pair control for limits below the cap -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_entropy_moment_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightFamily s₀ η K α γ d₀ q)
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
  have hbound := A.toCompactFamily.weak_limit_moment hs₀ hsmax hη hηmax hK.le hα
    (hαmax.trans (by norm_num)) hγ hd₀ hd₀max hsmall hq₂ hg S.nonnegative
  have hbase := momentBase_nonneg hs₀ hK.le hd₀ η α q
  have hgain := JetEnvelopeGain.momentConstant_nonneg hK.le α γ
  have hE := CollisionCompactness.exponentialPair_integrable S.measurable S.nonnegative
    (fun u => AnnularEnvelope.commonMoment_nonneg hbase hgain s₀ η (AnnularEnvelope.torusChart u))
    (AnnularEnvelope.torus_common_square_integrable hs₀ hη hηmax A.time_pos.le
      (momentBase s₀ η K α d₀ q) (JetEnvelopeGain.momentConstant K α γ)) hbound
  exact ⟨g,S,hfinite,hentropy,hE⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # A strongly continuous admissible local solution from approximations below the cap -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_admissible_local_solution
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (A : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 < K) (hα : 0 < α) (hαmax : α ≤ 1/4) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1) (hwidth : d₀*(1/8:ℝ)^10 ≤ 1/64)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ F : Evolution, AdmissibleLocal A.time (JetPeriodicDatum.datum s₀ η K α γ d₀) F := by
  obtain ⟨g,S,hfinite,hH,hE⟩ := A.exists_entropy_moment_mild_limit hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hwidth hsmall hq₁ hq₂
  have hf₀ := JetPeriodicDatum.finiteEntropy hs₀ hsmax hη hηmax hK hγ hd₀ hwidth hα.le hαmax
  have hm : Measurable (JetPeriodicDatum.datum s₀ η K α γ d₀) :=
    JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))
  have hn : ∀ p, 0 ≤ JetPeriodicDatum.datum s₀ η K α γ d₀ p :=
    fun p => JetDatumMoments.datum_nonneg hs₀ hK.le hd₀.le η α γ _
  exact ⟨_,S.localAdmissible A.time_pos hm hn hf₀ hfinite hH hE⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
