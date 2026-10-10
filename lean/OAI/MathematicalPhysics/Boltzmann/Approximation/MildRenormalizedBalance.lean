import OAI.MathematicalPhysics.Boltzmann.Approximation.MildRenormalization
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyIntegralBalance
import OAI.MathematicalPhysics.Boltzmann.Compactness.L1CurveEquality
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.StrongMildRepresentative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport

namespace OAI

section

/-! # The canonical integral paths agree with every-time physical traces -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem evolution_along_eq_path {t : ℝ} (ht : t ∈ Icc 0 T) (p : Phase) :
    evolution T f₀ g t (TorusFlight.flight t p) = entropyPath f₀ (characteristicSource g) t p := by
  unfold evolution TorusFlight.eulerianProfile
  rw [TorusFlight.flight_neg]
  change f₀ p+Published.timePrimitive (volume.restrict (Icc 0 T)) (characteristicSource g) (t,p) = _
  rw [Published.timePrimitive_eq_interval ht]
  rfl

theorem positiveEvolution_along_eq_path (S : MildCollisionSolution T f₀ g)
    (hT : 0 < T) (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun p => positiveEvolution T f₀ g t (TorusFlight.flight t p)) =ᵐ[volume]
      (fun p => entropyPath f₀ (characteristicSource g) t p) := by
  have h := (TorusFlight.flight_measurePreserving t).quasiMeasurePreserving.ae
    (S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht)
  filter_upwards [h] with p hp
  exact hp.symm.trans (evolution_along_eq_path ht p)

theorem positiveEvolution_along_eq_path_spacetime (S : MildCollisionSolution T f₀ g) :
    (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => entropyPath f₀ (characteristicSource g) z.1 z.2) := by
  have h := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae
    (S.evolution_eq_ae.symm.trans S.positiveEvolution_eq_ae)
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [h,ht] with z hz htz
  exact hz.symm.trans (evolution_along_eq_path htz z.2)

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Weak kinetic traces for a fixed nonlinear mild limit -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

theorem weak_kinetic_trace {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}
    (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    {u r : ℕ → (ℝ × Position) × Velocity → ℝ} {a : ℕ → Density}
    (hum : ∀ n, Measurable (u n)) (hrm : ∀ n, Measurable (r n))
    (hri : ∀ n, Integrable (r n) ((AnnularEnvelope.timePositionVolume T).prod volume))
    (ha : Published.WeakL1Converges volume a f₀) (hai : ∀ n, Integrable (a n))
    (hr : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume T).prod volume) r (source g))
    (t : ℝ) (ht : t ∈ Icc 0 T)
    (hchar : ∀ n, (fun p => u n ((t,(TorusFlight.flight t p).1),(TorusFlight.flight t p).2)) =ᵐ[volume]
      TorusFlight.characteristicProfile (volume.restrict (Icc 0 T)) (a n)
        (TorusFlight.along (TorusFlight.regroup (r n))) t) :
    Published.WeakL1Converges volume (fun n p => u n ((t,p.1),p.2)) (positiveEvolution T f₀ g t) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hrr := TorusFlight.weak_regroup hrm hr
  have hra := TorusFlight.weak_along
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hrr
  have hrain n : Integrable (TorusFlight.along (TorusFlight.regroup (r n)))
      (μ.prod (volume : Measure Phase)) := by
    have hi := (measurePreserving_prodAssoc μ (volume : Measure Position)
      (volume : Measure Velocity)).symm.integrable_comp_of_integrable (hri n)
    rw [Measure.volume_eq_prod] at ⊢
    exact (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hi
  have hw := TorusFlight.weak_of_characteristic_slice ha hai hra
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable |>.comp
      (TorusFlight.along_measurePreserving μ).measurable)
    hrain t (fun n => (hum n).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)) hchar
  have hm := S.positiveEvolution_measurable ha.1
  exact hw.congr_limit (hm.comp (measurable_const.prodMk measurable_id))
    (S.evolution_eq_positive_each_time hT ha.1 ha.2.1 t ht)

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # Every-time mass conservation for the constructed local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem source_mass_zero (S : MildCollisionSolution T f₀ g) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T),
      (∫ p : Phase, source g ((t,p.1),p.2)) = 0 := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hpi := (measurePreserving_prodAssoc μ (volume : Measure Position)
    (volume : Measure (Velocity × Velocity))).symm.integrable_comp_of_integrable S.pair_integrable
  filter_upwards [hpi.prod_right_ae] with t ht
  let f : Position × Velocity → ℝ := fun p => g ((t,p.1),p.2)
  have hm : Measurable f := S.measurable.comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hn : ∀ p, 0 ≤ f p := fun p => S.nonnegative _
  have hp : Integrable (CollisionCompactness.pairDensity f)
      ((volume : Measure Position).prod (volume : Measure (Velocity × Velocity))) := ht
  have hc := CollisionCompactness.gainLoss_integral_eq hm hn hp
  have hi := CollisionCompactness.gainLoss_integrable hm hn hp
  change (∫ p : Phase, CollisionCompactness.gainDensity f p-CollisionCompactness.lossDensity f p) = 0
  rw [Measure.volume_eq_prod,integral_sub hi.1 hi.2,hc,sub_self]

theorem characteristicSource_mass_zero (S : MildCollisionSolution T f₀ g) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), (∫ p : Phase, characteristicSource g (t,p)) = 0 := by
  filter_upwards [S.source_mass_zero] with t ht
  change (∫ p : Phase, (fun p => source g ((t,p.1),p.2)) (TorusFlight.flight t p)) = 0
  exact (TorusFlight.integral_flight (fun p => source g ((t,p.1),p.2)) t).trans ht

theorem mass_conservation (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ p, positiveEvolution T f₀ g t p) = ∫ p, f₀ p := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  have hz : (∫ p, Published.timePrimitive μ (characteristicSource g) (t,p)) = 0 := by
    rw [Published.integral_timePrimitive S.characteristicSource_integrable]
    apply integral_eq_zero_of_ae
    filter_upwards [S.characteristicSource_mass_zero] with s hs
    split_ifs <;> simp_all
  calc
    _ = ∫ p, evolution T f₀ g t p := integral_congr_ae
      (S.evolution_eq_positive_each_time hT hf₀m hf₀i t ht).symm
    _ = ∫ p, TorusFlight.characteristicProfile μ f₀ (characteristicSource g) t p :=
      TorusFlight.integral_flight _ (-t)
    _ = (∫ p, f₀ p)+(∫ p, Published.timePrimitive μ (characteristicSource g) (t,p)) :=
      integral_add hf₀i (TorusFlight.timePrimitive_slice_integrable
        S.characteristicSource_measurable S.characteristicSource_integrable t)
    _ = _ := by rw [hz,add_zero]

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The nonnegative strong representative satisfies the actual nonlinear mild equation -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

namespace Published

theorem timePrimitive_congr {P : Type*} [MeasurableSpace P]
    {μ : Measure ℝ} {ν : Measure P} [SFinite μ] [SFinite ν]
    {f g : ℝ × P → ℝ} (he : f =ᵐ[μ.prod ν] g) :
    timePrimitive μ f =ᵐ[μ.prod ν] timePrimitive μ g := by
  have hs := Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := μ)).quasiMeasurePreserving.ae he)
  have ht := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hs
  filter_upwards [ht] with z hz
  apply integral_congr_ae
  filter_upwards [hz] with s hs
  change f (s,z.2) = g (s,z.2) at hs
  rw [hs]

end Published

namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveDensity_source_eq_ae (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    source g =ᵐ[(AnnularEnvelope.timePositionVolume T).prod volume]
      source (kineticDensity (positiveEvolution T f₀ g)) := by
  have h := CollisionCompactness.gainLoss_congr
    S.measurable (S.positiveDensity_measurable hf₀) S.positiveDensity_eq_ae
  exact h.1.sub h.2

theorem positiveEvolution_characteristic (S : MildCollisionSolution T f₀ g)
    (hf₀ : Measurable f₀) :
    (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => f₀ z.2 + Published.timePrimitive (volume.restrict (Icc 0 T))
      (fun w => collision (positiveEvolution T f₀ g w.1)
        (TorusFlight.flight w.1 w.2).1 (TorusFlight.flight w.1 w.2).2) z) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  have hf : TorusFlight.regroup (kineticDensity F) =ᵐ[μ.prod volume] TorusFlight.regroup g :=
    S.positiveEvolution_eq_ae.symm
  have hs := (kineticGrouping_measurePreserving μ).symm.quasiMeasurePreserving.ae
    (S.positiveDensity_source_eq_ae hf₀)
  have ha : characteristicSource g =ᵐ[μ.prod volume] characteristicSource (kineticDensity F) :=
    (TorusFlight.along_measurePreserving μ).quasiMeasurePreserving.ae hs
  have hp := Published.timePrimitive_congr ha
  have hal : TorusFlight.along (TorusFlight.regroup (kineticDensity F)) =ᵐ[μ.prod volume]
      TorusFlight.along (TorusFlight.regroup g) :=
    (TorusFlight.along_measurePreserving μ).quasiMeasurePreserving.ae hf
  have he := hal.trans S.characteristic
  have heq : (fun w : ℝ × Phase => collision (F w.1)
      (TorusFlight.flight w.1 w.2).1 (TorusFlight.flight w.1 w.2).2) =
      characteristicSource (kineticDensity F) := by
    funext w
    exact (kineticDensity_collision F (w.1,TorusFlight.flight w.1 w.2)).symm
  filter_upwards [he,hp] with z hz hpz
  change F z.1 (TorusFlight.flight z.1 z.2) = f₀ z.2+Published.timePrimitive μ
    (characteristicSource g) z at hz
  rw [hpz] at hz
  change F z.1 (TorusFlight.flight z.1 z.2) = _
  rw [heq]
  exact hz

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

section

/-! # The physical renormalized collision term in characteristic coordinates -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveEvolution_along_collision_eq_source (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    characteristicSource g =ᵐ[(volume.restrict (Icc 0 T)).prod volume]
      (fun z => collision (positiveEvolution T f₀ g z.1)
        (TorusFlight.flight z.1 z.2).1 (TorusFlight.flight z.1 z.2).2) := by
  have hs := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.quasiMeasurePreserving.ae
    (S.positiveDensity_source_eq_ae hf₀m)
  have ha := (TorusFlight.along_measurePreserving (volume.restrict (Icc 0 T))).quasiMeasurePreserving.ae hs
  filter_upwards [ha] with z hz
  exact hz.trans (kineticDensity_collision _ (z.1,TorusFlight.flight z.1 z.2))

theorem renormalizedIntegrand_along_eq (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) (β : Renormalization) (φ : KineticTest) :
    TorusFlight.along (renormalizedIntegrand (positiveEvolution T f₀ g) β φ) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume]
      (fun z => derivWithin β.toFun (Ici 0)
          (entropyPath f₀ (characteristicSource g) z.1 z.2/maxwellian z.2.2)*
          characteristicSource g z*φ.toFun z.1 (TorusFlight.flight z.1 z.2).1 z.2.2+
        maxwellian z.2.2*β.toFun (entropyPath f₀ (characteristicSource g) z.1 z.2/maxwellian z.2.2)*
          φ.transportDerivative z.1 (TorusFlight.flight z.1 z.2)) := by
  filter_upwards [S.positiveEvolution_along_eq_path_spacetime,
    S.positiveEvolution_along_collision_eq_source hf₀m] with z hf hr
  dsimp only [TorusFlight.along,renormalizedIntegrand,relativeDensity]
  rw [hf,← hr]
  simp only [TorusFlight.flight]
  ring

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The actual strong representative has integrable renormalized weak terms -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem positiveEvolution_spacetime_integrable (S : MildCollisionSolution T f₀ g) :
    Integrable (fun z : ℝ × Phase => positiveEvolution T f₀ g z.1 z.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable
    S.integrable
  exact hi.congr S.positiveEvolution_eq_ae

theorem positiveEvolution_collision_integrable (S : MildCollisionSolution T f₀ g)
    (hf₀m : Measurable f₀) :
    Integrable (fun z : ℝ × Phase => collision (positiveEvolution T f₀ g z.1) z.2.1 z.2.2)
      ((volume.restrict (Icc 0 T)).prod volume) := by
  have hi := CollisionCompactness.gainLoss_integrable (S.positiveDensity_measurable hf₀m)
    (fun z => positiveEvolution_nonnegative z.1.1 (z.1.2,z.2))
    (S.positiveDensity_pair_integrable hf₀m)
  have h := (kineticGrouping_measurePreserving (volume.restrict (Icc 0 T))).symm.integrable_comp_of_integrable
    (hi.1.sub hi.2)
  exact h.congr (Filter.Eventually.of_forall (kineticDensity_collision _))

theorem renormalized_integrable (S : MildCollisionSolution T f₀ g) (hf₀m : Measurable f₀)
    (β : Renormalization) (φ : KineticTest) :
    IntegrableOn (renormalizedIntegrand (positiveEvolution T f₀ g) β φ) (boundedTimes T) :=
  renormalizedIntegrand_integrable (S.positiveEvolution_measurable hf₀m)
    positiveEvolution_nonnegative S.positiveEvolution_spacetime_integrable
    (S.positiveEvolution_collision_integrable hf₀m) β φ

end BoltzmannNonuniqueness.MildCollisionSolution

end

end

section

/-! # The weak renormalized equation for the actual local mild solution -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness



namespace MildCollisionSolution

variable {T : ℝ} {f₀ : Density} {g : (ℝ × Position) × Velocity → ℝ}

theorem renormalized_balance (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p)
    (β : Renormalization) (φ : KineticTest) :
    (∫ z in boundedTimes T, renormalizedIntegrand (positiveEvolution T f₀ g) β φ z) =
      (∫ p : Phase, maxwellian p.2*β.toFun (positiveEvolution T f₀ g T p/maxwellian p.2)*
        φ.toFun T p.1 p.2)-
      (∫ p : Phase, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let F := positiveEvolution T f₀ g
  let I := renormalizedIntegrand F β φ
  let B : Phase → ℝ := fun p => maxwellian p.2*β.toFun (F T p/maxwellian p.2)*φ.toFun T p.1 p.2
  let B₀ : Phase → ℝ := fun p => maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2
  have hIi : Integrable I (μ.prod volume) := by
    have h := S.renormalized_integrable hf₀m β φ
    change Integrable I _ at h
    rwa [← phaseInterval_measure] at h
  have hAi := (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hIi
  have hBm : Measurable (F T) := (S.positiveEvolution_measurable hf₀m).comp
    (measurable_const.prodMk measurable_id)
  have hBi : Integrable B := φ.weighted_slice_integrable β ⟨hT.le,le_rfl⟩ hBm
    (positiveEvolution_nonnegative T) (S.positiveEvolution_integrable hf₀m hf₀i T)
  have hB₀i : Integrable B₀ := φ.weighted_slice_integrable β ⟨le_rfl,hT.le⟩ hf₀m hf₀n hf₀i
  have hp : ∀ᵐ p : Phase,
      (∫ t, TorusFlight.along I (t,p) ∂μ) = B (TorusFlight.flight T p)-B₀ p := by
    have he := Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := (volume : Measure Phase)) (ν := μ)).quasiMeasurePreserving.ae
        (S.renormalizedIntegrand_along_eq hf₀m β φ))
    filter_upwards [S.renormalized_tested_paths hT β φ,he,
      S.positiveEvolution_along_eq_path hT hf₀m hf₀i ⟨hT.le,le_rfl⟩] with p hp he hend
    rw [intervalIntegral.integral_of_le hT.le,← integral_Icc_eq_integral_Ioc] at hp
    calc
      _ = _ := integral_congr_ae he
      _ = _ := hp
      _ = _ := by
        dsimp only [B,B₀,F]
        rw [hend]
        rfl
  calc
    _ = ∫ z, I z ∂μ.prod volume := by rw [phaseInterval_measure]
    _ = ∫ z, TorusFlight.along I z ∂μ.prod volume := (TorusFlight.integral_along hIi).symm
    _ = ∫ p : Phase, ∫ t, TorusFlight.along I (t,p) ∂μ := integral_prod_symm _ hAi
    _ = ∫ p : Phase, B (TorusFlight.flight T p)-B₀ p := integral_congr_ae hp
    _ = (∫ p : Phase, B (TorusFlight.flight T p))-(∫ p : Phase, B₀ p) :=
      integral_sub ((TorusFlight.flight_measurePreserving T).integrable_comp_of_integrable hBi) hB₀i
    _ = _ := by rw [TorusFlight.integral_flight]

theorem renormalized_equation_of_terminal_zero (S : MildCollisionSolution T f₀ g) (hT : 0 < T)
    (hf₀m : Measurable f₀) (hf₀i : Integrable f₀) (hf₀n : ∀ p, 0 ≤ f₀ p)
    (β : Renormalization) (φ : KineticTest) (hφ : ∀ x v, φ.toFun T x v = 0) :
    (∫ z in boundedTimes T, renormalizedIntegrand (positiveEvolution T f₀ g) β φ z)+
      (∫ p : Phase, maxwellian p.2*β.toFun (f₀ p/maxwellian p.2)*φ.toFun 0 p.1 p.2) = 0 := by
  rw [S.renormalized_balance hT hf₀m hf₀i hf₀n β φ]
  simp only [hφ,mul_zero,integral_zero,zero_sub,neg_add_cancel]

end MildCollisionSolution
end BoltzmannNonuniqueness

end

end

end OAI
