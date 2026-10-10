import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralPasting
import OAI.MathematicalPhysics.Boltzmann.Branching.HotCollisionDecomposition
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedHotRegularity
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions

namespace OAI

section

/-! # Almost-everywhere invariance of the colored forcing along spacetime -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

abbrev spacetimeVolume : Measure (ℝ × JetPrototype.Phase) :=
  (volume : Measure ℝ).prod FlightMeasure.phaseVolume

private theorem unstate_congr {f g : (ℝ × JetPrototype.Space) × Velocity → ℝ}
    (hfg : f =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume] g) :
    (fun u : ℝ × JetPrototype.Phase => f ((u.1,u.2.1),u.2.2)) =ᵐ[spacetimeVolume]
      (fun u : ℝ × JetPrototype.Phase => g ((u.1,u.2.1),u.2.2)) :=
  (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp hfg

theorem forcing_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) :
    forcing q b L F =ᵐ[spacetimeVolume] forcing q b L G :=
  unstate_congr (HotRepresentative.source_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume)
    (HotCanonical.state_congr hFG) q b L)

theorem coldForcing_congr_total {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) (c : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L G c :=
  unstate_congr (HotRepresentative.coldSource_congr_total
    ((volume : Measure ℝ).prod JetPrototype.spaceVolume) (HotCanonical.state_congr hFG) q b L
    (GaussianLocal.state c))

def remainderForcing {I : Type*} (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (c : I → ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  forcing q b L F u-∑' i, coldForcing q b L F (c i) u

theorem remainderForcing_congr {I : Type*} [Countable I] {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b L : ℝ) (c : I → ℝ × JetPrototype.Phase → ℝ) :
    remainderForcing q b L F c =ᵐ[spacetimeVolume] remainderForcing q b L G c := by
  have hc : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L F (c i) u = coldForcing q b L G (c i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_total hFG q b L (c i))
  filter_upwards [forcing_congr hFG q b L,hc] with u hfu hcu
  unfold remainderForcing
  rw [hfu]
  congr 1
  exact tsum_congr hcu

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Mild equations stable under changing spatial representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set

namespace BoltzmannNonuniqueness.WeightedLocal

/-- The mild identity on every time slice, with spatial null sets allowed to depend on time. -/
def MildAE (q b L T : ℝ) (f₀ : JetPrototype.Phase → ℝ)
    (F : ℝ × JetPrototype.Phase → ℝ) : Prop :=
  ∀ t ∈ Icc 0 T, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume]
    (fun p => PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) (t,p))

theorem mildAE_of_pointwise {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) u) :
    MildAE q b L T f₀ F := fun t _ => ae_of_all _ (fun p => hF (t,p))

theorem slice_congr_spacetime {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hFG : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => G (t,p))) :
    F =ᵐ[spacetimeVolume] G :=
  (ae_prod_iff_ae_ae (measurableSet_eq_fun hFm hGm)).mpr (ae_of_all _ hFG)

theorem MildAE.representative {q b L T : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F G : ℝ × JetPrototype.Phase → ℝ} (hF : MildAE q b L T f₀ F)
    (hFm : Measurable F) (hGm : Measurable G)
    (hFG : ∀ t, (fun p => F (t,p)) =ᵐ[FlightMeasure.phaseVolume] (fun p => G (t,p))) :
    MildAE q b L T f₀ G := by
  have hsource := forcing_congr (slice_congr_spacetime hFm hGm hFG) q b L
  intro t ht
  exact (hFG t).symm.trans ((hF t ht).trans
    (FlightMeasure.value_congr_at_time (ae_of_all _ (fun _ => rfl)) hsource T L t))

theorem canonical_mildAE {q b L T R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    {F : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hF : ∀ u, |F u| ≤ R)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p))))
    (hfix : ∀ u, F u = PositiveIntegral.value T L JetBarrier.flight f₀ (forcing q b L F) u) :
    MildAE q b L T f₀ (PhaseEssSup.canonical F) :=
  (mildAE_of_pointwise hfix).representative hFm (PhaseEssSup.measurable_canonical hFm hnorm)
    (fun t => (PhaseEssSup.canonical_ae_at_time hFm hF t).symm)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Vanishing labels stay absent from the cold iteration -/

noncomputable section

namespace BoltzmannNonuniqueness.WeightedLocal

theorem coldForcing_zero (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F 0 = 0 := by
  funext z
  simp [coldForcing,HotRepresentative.coldSource,HotRepresentative.gain,
    HotRepresentative.density,GaussianLocal.state,KineticCollisionNullSets.gain,
    CollisionCutoff.gain,CollisionCutoff.integrand]

theorem coldPicard_zero (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) (n : ℕ) :
    coldPicard q b L T F 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [coldPicard,ih,coldForcing_zero]
    funext z
    simp [PositiveIntegral.value]

theorem coldLimit_zero (q b L T : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldLimit q b L T F 0 = 0 := by
  funext z
  simp [coldLimit,coldPicard_zero]

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Cold-source equality and finite-family domination almost everywhere -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

theorem coldForcing_congr_cold {c d : ℝ × JetPrototype.Phase → ℝ}
    (hcd : c =ᵐ[spacetimeVolume] d) (q b L : ℝ) (F : ℝ × JetPrototype.Phase → ℝ) :
    coldForcing q b L F c =ᵐ[spacetimeVolume] coldForcing q b L F d := by
  have hs := HotCanonical.state_congr hcd
  have hg := HotRepresentative.gain_congr ((volume : Measure ℝ).prod JetPrototype.spaceVolume) hs q b
  have he : HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state c) =ᵐ[
      ((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      HotRepresentative.coldSource q b L (GaussianLocal.state F) (GaussianLocal.state d) := by
    filter_upwards [hs,hg] with u hu hgu
    unfold HotRepresentative.coldSource
    rw [hu,hgu]
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp he

theorem finite_coldForcing_le_ae {I : Type*} [Countable I] {q b L R : ℝ}
    (hq : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L) (s : Finset I)
    {F : ℝ × JetPrototype.Phase → ℝ} {c : I → ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hcm : ∀ i ∈ s, Measurable (c i))
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hc : ∀ i ∈ s, ∀ u, 0 ≤ c i u ∧ c i u ≤ R)
    (hSum : ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, c i u ≤ F u) :
    ∀ᵐ u ∂spacetimeVolume, ∑ i ∈ s, coldForcing q b L F (c i) u ≤ forcing q b L F u := by
  classical
  let d (i : I) (u : ℝ × JetPrototype.Phase) := if (∑ j ∈ s, c j u) ≤ F u then c i u else 0
  have hm : MeasurableSet {u : ℝ × JetPrototype.Phase | (∑ j ∈ s, c j u) ≤ F u} :=
    measurableSet_le (Finset.measurable_sum s hcm) hFm
  have hdm (i) (hi : i ∈ s) : Measurable (d i) := (hcm i hi).ite hm measurable_const
  have hdb (i) (hi : i ∈ s) (u) : 0 ≤ d i u ∧ d i u ≤ R := by
    dsimp [d]
    split_ifs
    · exact hc i hi u
    · exact ⟨le_rfl,hR⟩
  have hds (u) : (∑ i ∈ s, d i u) ≤ F u := by
    by_cases hu : (∑ i ∈ s, c i u) ≤ F u
    · simpa only [d,ite_eq_left hu] using hu
    · simpa only [d,ite_eq_right hu,Finset.sum_const_zero] using (hF u).1
  have hbound (u) : (∑ i ∈ s, coldForcing q b L F (d i) u) ≤ forcing q b L F u :=
    HotRepresentative.finite_sum_coldSource_le hq hb hloss s
      (fun i hi => GaussianLocal.measurable_state (hdm i hi)) (GaussianLocal.measurable_state hFm)
      (fun i hi p => hdb i hi (p.1.1,(p.1.2,p.2)))
      (fun p => hF (p.1.1,(p.1.2,p.2))) (fun p => hds (p.1.1,(p.1.2,p.2))) _
  have he (i : I) : d i =ᵐ[spacetimeVolume] c i := hSum.mono (fun u hu => ite_eq_left hu)
  have hce : ∀ᵐ u ∂spacetimeVolume, ∀ i, coldForcing q b L F (d i) u = coldForcing q b L F (c i) u :=
    ae_all_iff.mpr (fun i => coldForcing_congr_cold (he i) q b L F)
  filter_upwards [hce] with u hu
  have h := hbound u
  simpa only [hu] using h

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Pasting positive local solutions across an a.e. time slice -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeightedLocal

theorem measurable_paste {s : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : Measurable F) (hG : Measurable G) : Measurable (paste s F G) :=
  hF.ite (measurableSet_le measurable_fst measurable_const)
    (hG.comp ((measurable_fst.sub measurable_const).prodMk measurable_snd))

theorem paste_bounds {s R : ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (u : ℝ × JetPrototype.Phase) : 0 ≤ paste s F G u ∧ paste s F G u ≤ R := by
  unfold paste
  split_ifs
  · exact hF u
  · exact hG _

theorem paste_pull (s : ℝ) (F G : ℝ × JetPrototype.Phase → ℝ)
    (y : JetPrototype.Space) :
    WeightedTranslation.pull y (paste s F G) =
      paste s (WeightedTranslation.pull y F) (WeightedTranslation.pull y G) := rfl

theorem paste_mildAE {q b L s U S : ℝ} (hs : 0 ≤ s) (hU : 0 ≤ U) (hL : 0 ≤ L)
    {f₀ g₀ : JetPrototype.Phase → ℝ} {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hGm : Measurable G)
    (hsource : ∀ u, |forcing q b L (paste s F G) u| ≤ S)
    (hF : MildAE q b L s f₀ F) (hG : MildAE q b L U g₀ G)
    (hinit : g₀ =ᵐ[FlightMeasure.phaseVolume] (fun p => F (s,p))) :
    MildAE q b L (s+U) f₀ (paste s F G) := by
  have hprefix (t : ℝ) (ht : t ∈ Icc 0 s) (p : JetPrototype.Phase) :
      PositiveIntegral.value (s+U) L JetBarrier.flight f₀
          (forcing q b L (paste s F G)) (t,p) =
        PositiveIntegral.value s L JetBarrier.flight f₀ (forcing q b L F) (t,p) := by
    apply PositiveIntegral.value_eq_at_time ⟨ht.1,by linarith [ht.2]⟩ ht.2
    intro r hr p
    exact forcing_paste_left (hr.2.trans ht.2) F G q b L p
  intro t ht
  by_cases hts : t ≤ s
  · filter_upwards [hF t ⟨ht.1,hts⟩] with p hp
    rw [paste,ite_eq_left hts,hprefix t ⟨ht.1,hts⟩ p]
    exact hp
  · have hst : s < t := lt_of_not_ge hts
    have htu : t-s ∈ Icc 0 U := ⟨by linarith,by linarith [ht.2]⟩
    have hi := (FlightMeasure.flight_measurePreserving (s-t)).quasiMeasurePreserving.ae
      ((hF s ⟨hs,le_rfl⟩).symm.trans hinit.symm)
    filter_upwards [hG (t-s) htu,hi] with p hp hip
    have hr := PositiveIntegral.restart (add_nonneg hs hU) hL hs hst.le ht.2 f₀
      (measurable_forcing (measurable_paste hFm hGm) q b L) hsource p
    rw [hprefix s ⟨hs,le_rfl⟩,hip] at hr
    have hrest : (∫ r in s..t, Real.exp (-L*(t-r))*
        forcing q b L (paste s F G) (r,JetBarrier.flight (r-t) p)) =
        ∫ r in s..t, Real.exp (-L*(t-r))*
          forcing q b L G (r-s,JetBarrier.flight (r-t) p) := by
      apply intervalIntegral.integral_congr_ae
      apply ae_of_all
      intro r hr
      rw [uIoc_of_le hst.le] at hr
      rw [forcing_paste_right hr.1]
    rw [hrest,← PositiveIntegral.shifted_value htu] at hr
    rw [paste,ite_eq_right hts,hr]
    exact hp

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The cutoff source is Lipschitz for essentially close representatives -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeightedLocal

theorem forcing_difference_ae {q b L R D : ℝ} (hq : q < 2) (hb : 0 ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hD : 0 ≤ D)
    {F G : ℝ × JetPrototype.Phase → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    (hF : ∀ u, 0 ≤ F u ∧ F u ≤ R) (hG : ∀ u, 0 ≤ G u ∧ G u ≤ R)
    (hFG : ∀ᵐ u ∂spacetimeVolume, |F u-G u| ≤ D) :
    ∀ᵐ u ∂spacetimeVolume, |forcing q b L F u-forcing q b L G u| ≤
      (2*R*(HotApplication.realBound q+CutoffLipschitz.frequencyConstant q b)+L)*D := by
  let H (u : ℝ × JetPrototype.Phase) := max (G u-D) (min (F u) (G u+D))
  have hHm : Measurable H := (hGm.sub_const D).max (hFm.min (hGm.add_const D))
  have hHb (u) : 0 ≤ H u ∧ H u ≤ R := by
    dsimp [H]
    constructor
    · exact (le_min (hF u).1 (add_nonneg (hG u).1 hD)).trans (le_max_right _ _)
    · exact max_le (by linarith [(hG u).2]) ((min_le_left _ _).trans (hF u).2)
  have hHD (u) : |H u-G u| ≤ D := by
    rw [abs_sub_le_iff]
    dsimp [H]
    have hleft : G u-D ≤ max (G u-D) (min (F u) (G u+D)) := le_max_left _ _
    have hright : max (G u-D) (min (F u) (G u+D)) ≤ G u+D :=
      max_le (by linarith) (min_le_right _ _)
    constructor <;> linarith
  have hHF : H =ᵐ[spacetimeVolume] F := by
    filter_upwards [hFG] with u hu
    obtain ⟨h₁,h₂⟩ := abs_sub_le_iff.mp hu
    dsimp [H]
    rw [min_eq_left (by linarith),max_eq_right (by linarith)]
  have hsrc := forcing_congr hHF q b L
  filter_upwards [hsrc] with u hu
  rw [← hu]
  exact HotRepresentative.source_difference hq hb hL hR hD
    (GaussianLocal.measurable_state hHm) (GaussianLocal.measurable_state hGm)
    (fun p => hHb (p.1.1,(p.1.2,p.2))) (fun p => hG (p.1.1,(p.1.2,p.2)))
    (fun p => hHD (p.1.1,(p.1.2,p.2))) ((u.1,u.2.1),u.2.2)

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # Measurability and representative invariance of the physical loss frequency -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.WeightedLocal

def lossFrequency (q b : ℝ) (F : ℝ × JetPrototype.Phase → ℝ)
    (u : ℝ × JetPrototype.Phase) : ℝ :=
  HotRepresentative.frequency q b (GaussianLocal.state F) ((u.1,u.2.1),u.2.2)

theorem measurable_lossFrequency {F : ℝ × JetPrototype.Phase → ℝ}
    (hF : Measurable F) (q b : ℝ) : Measurable (lossFrequency q b F) :=
  (HotRepresentative.measurable_frequency (GaussianLocal.measurable_state hF) q b).comp
    (by fun_prop)

theorem lossFrequency_pull (q b : ℝ) (y : JetPrototype.Space) (F : ℝ × JetPrototype.Phase → ℝ) :
    lossFrequency q b (WeightedTranslation.pull y F) =
      WeightedTranslation.pull y (lossFrequency q b F) := rfl

theorem lossFrequency_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[spacetimeVolume] G) (q b : ℝ) :
    lossFrequency q b F =ᵐ[spacetimeVolume] lossFrequency q b G := by
  have h := HotRepresentative.frequency_congr
    ((volume : Measure ℝ).prod JetPrototype.spaceVolume) (HotCanonical.state_congr hFG) q b
  exact (MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
      (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp h

end BoltzmannNonuniqueness.WeightedLocal

end

end

section

/-! # The hot net source is bounded below by its physical loss -/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem hot_net_source_lower {q b R : ℝ} (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p) (p : X × Velocity) :
    -(frequency q b F p*(F p-∑' i, c i p)) ≤
      source q b L F p-(∑' i, coldSource q b L F (c i) p)-L*(F p-∑' i, c i p) := by
  have hg := (gain_family_summable (β := q) (b := b) hcm hFm hc hF hSum p).2
  rw [hot_source_identity L hcm hFm hc hF hSum]
  nlinarith only [hg]

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
