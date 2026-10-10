import Mathlib
import OAI.Analysis.CoulombIonization.Localization.DyadicObservation

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

def configurationSetoid (N : ℕ) : Setoid (Configuration N) where
  r x y := ∃ π : Equiv.Perm (Fin N), ∀ i, y i = x (π i)
  iseqv := {
    refl := fun _ => ⟨Equiv.refl _,fun _ => rfl⟩
    symm := by
      rintro x y ⟨π,hπ⟩
      exact ⟨π.symm,fun i => by simpa using (hπ (π.symm i)).symm⟩
    trans := by
      rintro x y z ⟨π,hπ⟩ ⟨τ,hτ⟩
      exact ⟨τ.trans π,fun i => (hτ i).trans (hπ (τ i))⟩ }

abbrev UnorderedConfiguration (N : ℕ) := Quotient (configurationSetoid N)

def unorderedConfiguration {N : ℕ} (x : Configuration N) : UnorderedConfiguration N :=
  Quotient.mk'' x

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

def unorderedStatistic {N : ℕ} (g : Space → ℝ) : UnorderedConfiguration N → ℝ :=
  Quotient.lift (fun x : Configuration N => ∑ i, g (x i)) (by
    rintro x y ⟨π,hπ⟩
    simp_rw [hπ]
    exact (Equiv.sum_comp π (fun i => g (x i))).symm)

@[simp] lemma unorderedStatistic_mk {N : ℕ} (g : Space → ℝ) (x : Configuration N) :
    unorderedStatistic g (unorderedConfiguration x) = ∑ i, g (x i) := rfl

lemma unorderedStatistic_measurable {N : ℕ} {g : Space → ℝ} (hg : Measurable g) :
    Measurable (unorderedStatistic (N := N) g) := by
  apply measurable_from_quotient.mpr
  change Measurable (fun x : Configuration N => ∑ i, g (x i))
  exact Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))

def physicalObservedConfiguration {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : Configuration N :=
  fun i => WithLp.toLp 2 (fun a => physicalObservationArray ell z (k,i,a))

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

def unorderedObservedConfiguration {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : UnorderedConfiguration N :=
  unorderedConfiguration (physicalObservedConfiguration ell k z)

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

@[instance_reducible] def observationInformation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :=
  ⨆ k : Fin K, if j ≤ k.val then
    MeasurableSpace.comap (unorderedObservedConfiguration ell k) inferInstance else ⊥

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

lemma observationInformation_antitone {N K : ℕ} (ell : Fin K → ℝ) :
    Antitone (observationInformation (N := N) ell) := by
  intro i j hij
  apply iSup_le
  intro k
  split_ifs with hk
  · exact le_iSup_of_le k (by rw [ite_eq_left (hij.trans hk)])
  · exact bot_le

lemma observationInformation_terminal {N K : ℕ} (ell : Fin K → ℝ) :
    observationInformation (N := N) ell K = ⊥ := by
  apply le_antisymm _ bot_le
  apply iSup_le
  intro k
  rw [ite_eq_right (not_le.mpr k.isLt)]

lemma observedStatistic_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} (hg : Measurable g) :
    Measurable[observationInformation ell j]
      (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
        ∑ i, g (physicalObservedConfiguration ell k z i)) := by
  have h := (unorderedStatistic_measurable (N := N) hg).comp
    (comap_measurable (unorderedObservedConfiguration (N := N) ell k))
  apply h.mono
  · exact le_iSup_of_le k (by rw [ite_eq_left hk])
  · exact le_refl _

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

namespace CoulombObservation

lemma compactNoiseLaw_ae_support : ∀ᵐ u ∂compactNoiseLaw, |u| < 1 := by
  rw [compactNoiseLaw,ae_withDensity_iff compactNoiseDensity_measurable.ennreal_ofReal]
  apply ae_of_all
  intro u hu
  by_contra hn
  exact hu (by simp [compactNoiseDensity,compactNoiseWeight,hn])

lemma compactNoiseLaw_pi_ae_support {ι : Type*} [Fintype ι] :
    ∀ᵐ u ∂Measure.pi (fun _ : ι => compactNoiseLaw), ∀ i, |u i| < 1 :=
  eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => compactNoiseLaw) (i := i)).eventually
      compactNoiseLaw_ae_support)

end CoulombObservation
namespace CoulombAtom
open CoulombObservation

def physicalObservationLaw {N : ℕ} (μ : Measure (Configuration N)) (K : ℕ) :
    Measure (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :=
  μ.prod (Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))

instance physicalObservationLaw_finite {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : IsFiniteMeasure (physicalObservationLaw μ K) := by
  unfold physicalObservationLaw
  infer_instance

lemma physicalObservationLaw_probability {N K : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (physicalObservationLaw μ K) := by
  unfold physicalObservationLaw
  infer_instance

lemma physicalObservedConfiguration_displacement {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (hk : 0 ≤ ell k) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hu : ∀ q, |z.2 q| < 1) (i : Fin N) :
    ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have he (a : Fin 3) : (physicalObservedConfiguration ell k z i-z.1 i) a =
      ell k*z.2 (k,i,a) := by
    change (z.1 i a+ell k*z.2 (k,i,a))-z.1 i a = _
    ring
  have hs : ‖physicalObservedConfiguration ell k z i-z.1 i‖^2 ≤ 3*(ell k)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp_rw [he]
    calc
      _ ≤ ∑ _a : Fin 3, (ell k)^2 := by
        apply Finset.sum_le_sum
        intro a _
        have hsq : (z.2 (k,i,a))^2 ≤ 1 := by
          have := hu (k,i,a)
          have := abs_nonneg (z.2 (k,i,a))
          nlinarith [sq_abs (z.2 (k,i,a))]
        rw [mul_pow]
        exact (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)).trans_eq (mul_one _)
      _ = _ := by simp
  have hs3 : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 ≤ Real.sqrt 3*ell k := mul_nonneg (Real.sqrt_nonneg _) hk
  nlinarith [sq_nonneg (‖physicalObservedConfiguration ell k z i-z.1 i‖-Real.sqrt 3*ell k)]

lemma physicalObservationLaw_ae_displacement {N K : ℕ} (μ : Measure (Configuration N))
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ k i,
      ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := μ)
    (ν := Measure.pi (fun _ : Fin K × (Fin N × Fin 3) => compactNoiseLaw))).tendsto_ae.eventually
      compactNoiseLaw_pi_ae_support
  exact h.mono (fun z hz k i => physicalObservedConfiguration_displacement ell k (hell k) z hz i)

def observedLocalCount {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) (R : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : ℝ :=
  ∑ i, if ‖physicalObservedConfiguration ell k z i-y‖ ≤ R then 1 else 0

lemma observedLocalCount_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) (R : ℝ) :
    Measurable[observationInformation ell j] (observedLocalCount (N := N) ell k y R) := by
  exact observedStatistic_information_measurable ell k hk
    (measurable_const.ite (measurableSet_le (show Measurable (fun x : Space => ‖x-y‖) by fun_prop) measurable_const) measurable_const)

lemma observedLocalCount_nonneg {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : 0 ≤ observedLocalCount ell k y R z := by
  unfold observedLocalCount
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)

lemma observedLocalCount_le {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : observedLocalCount ell k y R z ≤ N := by
  calc
    _ ≤ ∑ _i : Fin N, (1:ℝ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> norm_num)
    _ = N := by simp

lemma matchedLocal_test_error {N : ℕ} (x u : Configuration N) {δ R : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, ‖u i-x i‖ ≤ δ) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (hs : Function.support g ⊆ closedBall y R) :
    |(∑ i, g (x i))-(∑ i, g (u i))| ≤
      (∑ i, if ‖u i-y‖ ≤ R+δ then (1:ℝ) else 0)*((L:ℝ)*δ) := by
  classical
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |g (x i)-g (u i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (if ‖u i-y‖ ≤ R+δ then (1:ℝ) else 0)*((L:ℝ)*δ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs with hi
      · simp only [one_mul]
        exact (hg.dist_le_mul (x i) (u i)).trans
          (mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm,norm_sub_rev] using hx i) L.coe_nonneg)
      · have hu : g (u i) = 0 := by
          apply Function.notMem_support.mp
          intro hu
          have ha := hs hu
          simp only [mem_closedBall,dist_eq_norm] at ha
          exact hi (by linarith)
        have hx0 : g (x i) = 0 := by
          apply Function.notMem_support.mp
          intro h0
          have ha := hs h0
          simp only [mem_closedBall,dist_eq_norm] at ha
          have ht := norm_add_le (u i-x i) (x i-y)
          rw [sub_add_sub_cancel] at ht
          exact hi (by linarith [hx i])
        simp [hu,hx0]
    _ = _ := by rw [Finset.sum_mul]

end CoulombAtom

end

end OAI
