import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalization
import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalizedBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.Moments
import OAI.MathematicalPhysics.Boltzmann.Branching.MomentumCollisionIntegrability
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedMildBalance
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationAverage
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyDissipationCoordinates
import OAI.MathematicalPhysics.Boltzmann.Compactness.LocalMomentIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Integrable local mass tests and cancellation of their collision source -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def massTestIntegrand (F : Evolution) (φ : MassTest) (z : ℝ × Phase) : ℝ :=
  F z.1 z.2*φ.transportDerivative z.1 z.2+
    collision (F z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1

theorem MassTest.slice_integrable (φ : MassTest) {T t : ℝ} (ht : t ∈ Icc 0 T)
    {f : Density} (hfi : Integrable f) : Integrable (fun p => f p*φ.toFun t p.1) := by
  have hφ : Measurable (fun p : Phase => φ.toFun t p.1) :=
    φ.measurable_toFun.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply hfi.mul_bdd hφ.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [Real.norm_eq_abs] using (hb t ht p).1)

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem mass_source_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (φ : MassTest) :
    Integrable (fun z : ℝ × Phase => collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*
      φ.toFun z.1 z.2.1) ((volume.restrict (Icc 0 T)).prod volume) := by
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  apply (S.positiveEvolution_collision_integrable hf₀m).mul_bdd φ.measurable_toFun.aestronglyMeasurable
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with z hz
  simpa only [Real.norm_eq_abs] using (hb z.1 hz z.2).1

theorem mass_source_zero (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (φ : MassTest) :
    (∫ z : ℝ × Phase, collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*
      φ.toFun z.1 z.2.1 ∂(volume.restrict (Icc 0 T)).prod volume) = 0 := by
  let F := positiveEvolution T f₀ g
  let ψ : ℝ × Position → ℝ := fun u => φ.toFun u.1 u.2
  have hψm : Measurable ψ := φ.measurable_toFun.comp
    (show Measurable (fun u : ℝ × Position => (u.1,(u.2,(0:Velocity)))) from by fun_prop)
  obtain ⟨C,_hC,hb⟩ := φ.bounded_on_time T
  have hψb : ∀ᵐ u ∂AnnularEnvelope.timePositionVolume T, ‖ψ u‖ ≤ C := by
    have ht : ∀ᵐ u : ℝ × Position ∂AnnularEnvelope.timePositionVolume T, u.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [ht] with u hu
    simpa only [ψ,Real.norm_eq_abs] using (hb u.1 hu (u.2,0)).1
  have hz := CollisionCompactness.base_test_collision_zero (S.positiveDensity_measurable hf₀m)
    (fun p => positiveEvolution_nonnegative p.1.1 (p.1.2,p.2))
    (S.positiveDensity_pair_integrable hf₀m) hψm hψb
  let W : ℝ × Phase → ℝ := fun z => collision (F z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1
  have hc := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).integral_comp
    MeasurableEquiv.prodAssoc.measurableEmbedding W
  change (∫ z, W z ∂(volume.restrict (Icc 0 T)).prod volume) = 0
  rw [← hc]
  calc
    _ = ∫ p, ψ p.1*(CollisionCompactness.gainDensity (kineticDensity F) p-
        CollisionCompactness.lossDensity (kineticDensity F) p)
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
      apply integral_congr_ae
      filter_upwards [] with p
      have he := kineticDensity_collision F (p.1.1,(p.1.2,p.2))
      change collision (F p.1.1) p.1.2 p.2*ψ p.1 = _
      rw [← he]
      exact mul_comm _ _
    _ = 0 := hz

theorem mass_integrand_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    Integrable (massTestIntegrand (positiveEvolution T f₀ g) φ)
      ((volume.restrict (Icc 0 T)).prod volume) :=
  (mass_transport_integrable (S.positiveEvolution_measurable hf₀m) positiveEvolution_nonnegative hEi φ).add
    (S.mass_source_integrable hf₀m φ)

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The actual local mild solution conserves local mass -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem massTestIntegrand_along_eq (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (φ : MassTest) :
    TorusFlight.along (massTestIntegrand (positiveEvolution T f₀ g) φ) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => characteristicSource g z*φ.toFun z.1 (TorusFlight.flight z.1 z.2).1+
        entropyPath f₀ (characteristicSource g) z.1 z.2*
          φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)) := by
  filter_upwards [S.positiveEvolution_along_eq_path_spacetime,
    S.positiveEvolution_along_collision_eq_source hf₀m] with z hf hr
  dsimp only [TorusFlight.along,massTestIntegrand]
  rw [hf,← hr]
  exact add_comm _ _

theorem mass_balance_with_source (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    (∫ z, massTestIntegrand (positiveEvolution T f₀ g) φ z ∂(volume.restrict (Icc 0 T)).prod volume) =
      (∫ p : Phase, positiveEvolution T f₀ g T p*φ.toFun T p.1)-
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  let I := massTestIntegrand F φ
  let B : Phase → ℝ := fun p => F T p*φ.toFun T p.1
  let B₀ : Phase → ℝ := fun p => f₀ p*φ.toFun 0 p.1
  have hIi : Integrable I (μ.prod volume) := S.mass_integrand_integrable hf₀m hEi φ
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hBi : Integrable B := φ.slice_integrable ⟨hT.le,le_rfl⟩ (S.positiveEvolution_integrable hf₀m hf₀i T)
  have hB₀i : Integrable B₀ := φ.slice_integrable ⟨le_rfl,hT.le⟩ hf₀i
  have hp : ∀ᵐ p : Phase,
      (∫ t, TorusFlight.along I (t,p) ∂μ) = B (TorusFlight.flight T p)-B₀ p := by
    have he := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae
        (S.massTestIntegrand_along_eq hf₀m φ))
    filter_upwards [S.mass_tested_paths hT φ,he,
      S.positiveEvolution_along_eq_path hT hf₀m hf₀i ⟨hT.le,le_rfl⟩] with p hp he hend
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at hp
    calc
      _ = _ := integral_congr_ae he
      _ = _ := hp
      _ = _ := by
        dsimp only [B,B₀,F]
        rw [hend]
  calc
    _ = ∫ z, TorusFlight.along I z ∂μ.prod volume := (TorusFlight.integral_along hIi).symm
    _ = ∫ p : Phase, ∫ t, TorusFlight.along I (t,p) ∂μ := integral_prod_symm _ hAi
    _ = ∫ p : Phase, B (TorusFlight.flight T p)-B₀ p := integral_congr_ae hp
    _ = (∫ p : Phase, B (TorusFlight.flight T p))-(∫ p : Phase, B₀ p) :=
      integral_sub ((TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hBi) hB₀i
    _ = _ := by rw [TorusFlight.integral_flight]

theorem local_mass_balance (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest) :
    (∫ z in boundedTimes T, positiveEvolution T f₀ g z.1 z.2*φ.transportDerivative z.1 z.2) =
      (∫ p : Phase, positiveEvolution T f₀ g T p*φ.toFun T p.1)-
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) := by
  have h := S.mass_balance_with_source hT hf₀m hf₀i hEi φ
  change (∫ z, positiveEvolution T f₀ g z.1 z.2*φ.transportDerivative z.1 z.2+
    collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2*φ.toFun z.1 z.2.1
    ∂(volume.restrict (Icc 0 T)).prod volume) = _ at h
  rw [integral_add (mass_transport_integrable (S.positiveEvolution_measurable hf₀m)
      positiveEvolution_nonnegative hEi φ) (S.mass_source_integrable hf₀m φ),
    S.mass_source_zero hf₀m φ,add_zero] at h
  rwa [phaseInterval_measure] at h

theorem local_mass_of_terminal_zero (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hEi : Integrable (fun z : ℝ × Phase => entropyMoment (positiveEvolution T f₀ g z.1) z.2)
      ((volume.restrict (Icc 0 T)).prod volume)) (φ : MassTest)
    (hφ : ∀ x, φ.toFun T x = 0) :
    (∫ z in boundedTimes T, positiveEvolution T f₀ g z.1 z.2*φ.transportDerivative z.1 z.2)+
      (∫ p : Phase, f₀ p*φ.toFun 0 p.1) = 0 := by
  rw [S.local_mass_balance hT hf₀m hf₀i hEi φ]
  simp only [hφ,mul_zero,integral_zero,zero_sub,neg_add_cancel]

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Every-time energy conservation of the constructed local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem energy_source_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ‖p.2‖^2*source g ((t,p.1),p.2)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hpi := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable hE
  filter_upwards [hpi.prod_right_ae] with t ht
  let f : Position × Velocity → ℝ := fun p => g ((t,p.1),p.2)
  have hm : Measurable f := S.measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hn : ∀ p, 0 ≤ f p := fun p => S.nonnegative _
  have hp : Integrable (CollisionCompactness.exponentialPair f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := ht
  have hc := CollisionCompactness.energy_collision_balance hm hn hp
  have hi := CollisionCompactness.gainLoss_energy_integrable hm hn hp
  change (∫ p : Phase, ‖p.2‖^2*(CollisionCompactness.gainDensity f p-
    CollisionCompactness.lossDensity f p)) = 0
  simp_rw [mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2,hc,sub_self]

theorem energy_characteristic_integrable (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    Integrable (fun z : ℝ × Phase => ‖z.2.2‖^2*characteristicSource g z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_energy_integrable S.measurable S.nonnegative hE
  have hs : Integrable (fun p => ‖p.2‖^2*source g p)
      ((AnnularEnvelope.timePositionVolume T).prod volume) := by
    convert hi.1.sub hi.2 using 1
    funext p
    exact mul_sub _ _ _
  have hr := (measurePreserving_prodAssoc (volume.restrict (Icc 0 T))
    (volume : Measure Position) (volume : Measure Velocity)).symm.integrable_comp_of_integrable hs
  have hrr : Integrable (fun z : ℝ × Phase => ‖z.2.2‖^2*TorusFlight.regroup (source g) z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
    rw [Measure.volume_eq_prod]
    exact hr
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hrr

theorem energy_characteristic_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, ‖p.2‖^2*characteristicSource g (t,p)) = 0 := by
  filter_upwards [S.energy_source_zero hE] with t ht
  exact (TorusFlight.integral_flight
    (fun p : Phase => ‖p.2‖^2*source g ((t,p.1),p.2)) t).trans ht

theorem energy_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀)
    (hf₀E : Integrable (fun p : Phase => ‖p.2‖^2*f₀ p))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    energy (positiveEvolution T f₀ g t) = energy f₀ := by
  have hm : Measurable (fun z : ℝ × Phase => ‖z.2.2‖^2*characteristicSource g z) :=
    (measurable_snd.snd.norm.pow_const 2).mul S.characteristicSource_measurable
  have h := TorusFlight.velocity_weighted_profile_balance f₀ (characteristicSource g)
    (fun v => ‖v‖^2) hm (S.energy_characteristic_integrable hE) hf₀E t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, ‖p.2‖^2*characteristicSource g (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [S.energy_characteristic_zero hE] with s hs
    split_ifs <;> simp_all
  rw [hz,add_zero] at h
  change (∫ p : Phase, ‖p.2‖^2*positiveEvolution T f₀ g t p) = _
  calc
    _ = ∫ p : Phase, ‖p.2‖^2*evolution T f₀ g t p := by
      apply integral_congr_ae
      filter_upwards [S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht] with p hp
      rw [hp]
    _ = _ := h

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Entropy admissibility of the positive representative of a mild solution -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem entropy_admissible {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T) (hf₀ : FiniteEntropyDatum f₀)
    (hm₀ : Measurable f₀) (hn₀ : ∀ z, 0 ≤ f₀ z)
    (hH : ∀ t ∈ Ioc 0 T,
      (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (positiveEvolution T f₀ g t z)))+
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g ≤
          ENNReal.ofReal (relativeEntropy f₀)) :
    (∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t)) ∧
    (∀ t ∈ Icc 0 T, ENNReal.ofReal (relativeEntropy (positiveEvolution T f₀ g t))+
      (∫⁻ s in Icc (0:ℝ) t, entropyDissipation (positiveEvolution T f₀ g s)) ≤
        ENNReal.ofReal (relativeEntropy f₀)) := by
  let F := positiveEvolution T f₀ g
  have hFm := S.positiveEvolution_measurable hm₀
  have hFn : ∀ t z, 0 ≤ F t z := fun t z => positiveEvolution_nonnegative t z
  have hFi t : Measurable (F t) := hFm.comp (measurable_const.prodMk measurable_id)
  have hInitial : F 0 = f₀ := funext (positiveEvolution_initial hT.le hn₀)
  have hHintegrable {t : ℝ} (ht : t ∈ Icc 0 T) :
      Integrable (fun z => scalarRelativeEntropy (maxwellian z.2) (F t z)) := by
    by_cases ht0 : t = 0
    · rw [ht0,hInitial]
      exact hf₀.integrable_relativeEntropy.congr (ae_of_all _ (fun z =>
        (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
    · have htt : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
      have hfin : (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2) (F t z))) ≤
          ENNReal.ofReal (relativeEntropy f₀) :=
        (le_add_of_nonneg_right zero_le).trans (hH t htt)
      have hmm : Measurable (fun z : Phase => maxwellian z.2) := by
        unfold maxwellian
        fun_prop
      have hm : Measurable (fun z => scalarRelativeEntropy (maxwellian z.2) (F t z)) := by
        unfold scalarRelativeEntropy
        exact (((hFi t).mul (hFi t).log).sub ((hFi t).mul
          (measurable_const.add hmm.log))).add hmm
      exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
        (ae_of_all _ (fun z => scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hFn t z)))).mp
          (ne_of_lt (hfin.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨fun t ht => finiteEntropy_of_relativeEntropy_integrable (hFi t) (hFn t) (hHintegrable ht),?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · change ENNReal.ofReal (relativeEntropy (F t))+_ ≤ _
    simp [ht0,hInitial]
  · have htt : t ∈ Ioc 0 T := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
    have he : relativeEntropy (F t) = ∫ z, scalarRelativeEntropy (maxwellian z.2) (F t z) :=
      integral_congr_ae (ae_of_all _ (fun z => (scalarRelativeEntropy_eq (maxwellian_pos z.2) _).symm))
    have hD : CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) g =
        CollisionCompactness.rateDissipation (AnnularEnvelope.timePositionVolume t) (kineticDensity F) :=
      CollisionCompactness.rateDissipation_congr S.measurable (S.positiveDensity_measurable hm₀)
        (S.positiveDensity_eq_ae.filter_mono (ae_mono
          (Measure.prod_mono (timePositionVolume_mono ht.2) le_rfl)))
    rw [kineticDensity_rateDissipation hFm hFn t] at hD
    change ENNReal.ofReal (relativeEntropy (F t))+_ ≤ _
    rw [he,ofReal_integral_eq_lintegral_ofReal (hHintegrable ht)
      (ae_of_all _ (fun z => scalarRelativeEntropy_nonneg (maxwellian_pos z.2) (hFn t z))),← hD]
    exact hH t htt

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Every-time momentum conservation for the actual local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem coordinate_source_zero (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) (i : Fin 3) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, p.2 i*source g ((t,p.1),p.2)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hp := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable S.pair_integrable
  have he := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable hE
  filter_upwards [hp.prod_right_ae,he.prod_right_ae] with t hpt het
  let f : Position × Velocity → ℝ := fun p => g ((t,p.1),p.2)
  have hm : Measurable f := S.measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hn : ∀ p, 0 ≤ f p := fun p => S.nonnegative _
  have hpair : Integrable (CollisionCompactness.pairDensity f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := hpt
  have henergy : Integrable (CollisionCompactness.exponentialPair f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := het
  have hc := CollisionCompactness.momentum_collision_balance hm hn hpair henergy i
  have hi := CollisionCompactness.gainLoss_coordinate_integrable hm hn hpair henergy i
  change (∫ p : Phase, p.2 i*(CollisionCompactness.gainDensity f p-CollisionCompactness.lossDensity f p)) = 0
  simp_rw [mul_sub]
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2,hc,sub_self]

theorem coordinate_characteristic_integrable (S : MildCollisionSolution T f₀ g)
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume)) (i : Fin 3) :
    Integrable (fun z : ℝ × Phase => z.2.2 i*characteristicSource g z)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_coordinate_integrable S.measurable S.nonnegative S.pair_integrable hE i
  have hs : Integrable (fun p => p.2 i*source g p) ((AnnularEnvelope.timePositionVolume T).prod volume) := by
    convert hi.1.sub hi.2 using 1
    funext p
    exact mul_sub _ _ _
  have hr := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable hs
  exact (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).integrable_comp_of_integrable hr

theorem coordinate_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) {i : Fin 3}
    (hf₀c : Integrable (fun p : Phase => p.2 i*f₀ p))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p : Phase, p.2 i*positiveEvolution T f₀ g t p) = ∫ p : Phase, p.2 i*f₀ p := by
  have hm : Measurable (fun z : ℝ × Phase => z.2.2 i*characteristicSource g z) := by
    exact (by fun_prop : Measurable (fun z : ℝ × Phase => z.2.2 i)).mul S.characteristicSource_measurable
  have h := TorusFlight.velocity_weighted_profile_balance f₀ (characteristicSource g)
    (fun v => v i) hm (S.coordinate_characteristic_integrable hE i) hf₀c t
  have hz : (∫ s, if s ≤ t then ∫ p : Phase, p.2 i*characteristicSource g (s,p) else 0
      ∂volume.restrict (Icc 0 T)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [S.coordinate_source_zero hE i] with s hs
    have hchar : (∫ p : Phase, p.2 i*characteristicSource g (s,p)) = 0 :=
      (TorusFlight.integral_flight (fun p : Phase => p.2 i*source g ((s,p.1),p.2)) s).trans hs
    split_ifs <;> simp_all
  rw [hz,add_zero] at h
  calc
    _ = ∫ p : Phase, p.2 i*evolution T f₀ g t p := by
      apply integral_congr_ae
      filter_upwards [S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht] with p hp
      rw [hp]
    _ = _ := h

theorem momentum_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀ : FiniteEntropyDatum f₀)
    (hfinite : ∀ t ∈ Icc 0 T, FiniteEntropyDatum (positiveEvolution T f₀ g t))
    (hE : Integrable (CollisionCompactness.exponentialPair g)
      ((AnnularEnvelope.timePositionVolume T).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) : momentum (positiveEvolution T f₀ g t) = momentum f₀ := by
  apply PiLp.ext
  intro i
  let L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i
  have h₀ := L.integrable_comp hf₀.integrable_momentum
  have h₁ := L.integral_comp_comm hf₀.integrable_momentum
  have h₂ := L.integral_comp_comm (hfinite t ht).integrable_momentum
  have hc : Integrable (fun p : Phase => p.2 i*f₀ p) := by
    simpa only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul,mul_comm] using h₀
  have h := S.coordinate_conservation hT hf₀m hf₀.integrable hc hE ht
  change (momentum (positiveEvolution T f₀ g t)) i = (momentum f₀) i
  simp only [L,PiLp.proj_apply,PiLp.smul_apply,smul_eq_mul] at h₁ h₂
  calc
    _ = ∫ p : Phase, positiveEvolution T f₀ g t p*p.2 i := h₂.symm
    _ = ∫ p : Phase, p.2 i*positiveEvolution T f₀ g t p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
    _ = ∫ p : Phase, p.2 i*f₀ p := h
    _ = ∫ p : Phase, f₀ p*p.2 i := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun p => mul_comm _ _)
    _ = _ := h₁

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

end OAI
