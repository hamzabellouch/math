import Mathlib
import OAI.Analysis.CoulombIonization.Localization.FreshObservedSandwichBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.TailInitialEventuallyBarrier
import OAI.Analysis.CoulombIonization.Ionization.PricedAnnularCountBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

open CoulombBarrier
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

def observedAnnularCount {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) (a b : ℝ)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) : ℝ :=
  rawAnnularCount a b (physicalObservedConfiguration ell k z)

lemma observedAnnularCount_information_measurable {N K : ℕ} (ell : Fin K → ℝ)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (a b : ℝ) :
    Measurable[observationInformation ell j] (observedAnnularCount (N := N) ell k a b) := by
  unfold observedAnnularCount rawAnnularCount
  exact observedStatistic_information_measurable ell k hk
    (g := fun x : Space => if a ≤ ‖x‖ ∧ ‖x‖ ≤ b then 1 else 0) (measurable_const.ite (measurableSet_le measurable_const measurable_norm |>.inter
    (measurableSet_le measurable_norm measurable_const)) measurable_const)

lemma observed_annular_count_le_raw {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (a b : ℝ) (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    observedAnnularCount ell k a b z ≤
      rawAnnularCount (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) z.1 := by
  unfold observedAnnularCount rawAnnularCount
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_sub_norm_le (physicalObservedConfiguration ell k z i) (z.1 i)
    have ht' := norm_sub_norm_le (z.1 i) (physicalObservedConfiguration ell k z i)
    rw [norm_sub_rev] at ht'
    exact False.elim (hj ⟨by linarith [hd i,hi.1],by linarith [hd i,hi.2]⟩)
  · norm_num
  · exact le_rfl

lemma rawAnnularMoment_eq_integral {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (a b : ℝ) : rawAnnularMoment ψ a b = ∫ x, rawAnnularCount a b x^2 ∂formRawLaw ψ :=
  rawFormPair_eq_integral hψ ((rawAnnularCount_measurable a b).pow_const 2)
    (fun x => norm_sq_le_of_nonneg (rawAnnularCount_nonneg a b x) (rawAnnularCount_le a b x))

lemma rawAnnularCount_sq_integrable {N : ℕ} (a b : ℝ) (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] : Integrable (fun x => rawAnnularCount a b x^2) μ := by
  apply Integrable.mono' (integrable_const ((N:ℝ)^2))
    ((rawAnnularCount_measurable a b).pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x => norm_sq_le_of_nonneg (rawAnnularCount_nonneg a b x) (rawAnnularCount_le a b x))

lemma event_raw_annular_count_lower {N K : ℕ} (F G : fermionGraph N)
    (hGn : ‖fermionGraphValue N G‖^2 = 1) (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    (k : Fin K) (a b : ℝ) {T : ℝ} (hT : 0 ≤ T)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet A) (hcount : ∀ z ∈ A, T ≤ observedAnnularCount ell k a b z)
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A)) :
    T^2 ≤ rawAnnularMoment (graphFormVector G) (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) := by
  have he := event_rawLaw_ae F G ell hlaw
    (measurableSet_le measurable_const (rawAnnularCount_measurable _ _)) hA
    (by
      filter_upwards [physicalObservationLaw_ae_displacement (graphRawLaw F) ell hell] with z hz
      intro hzA
      exact (hcount z hzA).trans (observed_annular_count_le_raw ell k a b z (hz k)))
  let := graphRawLaw_probability G hGn
  rw [rawAnnularMoment_eq_integral (graphFormVector_sobolev G).sobolevVector,formRawLaw_graph]
  calc
    T^2 = ∫ _x : Configuration N, T^2 ∂graphRawLaw G := by simp
    _ ≤ ∫ x, rawAnnularCount (a-Real.sqrt 3*ell k) (b+Real.sqrt 3*ell k) x^2 ∂graphRawLaw G :=
      integral_mono_ae (integrable_const _) (rawAnnularCount_sq_integrable _ _ _)
        (he.mono (fun x hx => pow_le_pow_left₀ hT hx 2))

end Work_ObservedAnnularCount_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

open CoulombBarrier CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma annularOffsetMass_one_small {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (annularOffsetMass 1 r)^2 ≤ 4*r^(-6:ℝ) := by
  have hpow : r^3 ≤ 1 := pow_le_one₀ hr.le hr1
  have hi : 1 ≤ 1/r^3 := (one_le_div (pow_pos hr 3)).mpr hpow
  have hs : Real.sqrt r ≤ 1 := (Real.sqrt_le_one).mpr hr1
  have hm : annularOffsetMass 1 r ≤ 2*(1/r^3) := by
    simp only [annularOffsetMass,one_mul,max_eq_left hi]
    linarith only [hi,hs]
  have hmn : 0 ≤ annularOffsetMass 1 r := (zero_le_one.trans (annularOffsetMass_one_le 1 r))
  have he : (2*(1/r^3))^2 = 4*r^(-6:ℝ) := by
    rw [Real.rpow_neg hr.le,Real.rpow_ofNat]
    field_simp
    ring
  exact (pow_le_pow_left₀ hmn hm 2).trans_eq he

theorem exists_actual_priced_moment_constant :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Z lam : ℝ} {N : ℕ}, 0 ≤ Z → 0 < lam →
      PriceMinimizes (energy Z) lam N → ∀ F : fermionGraph N,
      ‖fermionGraphValue N F‖^2 = 1 →
      formEnergy Z (graphFormVector F) ≤ energy Z N+1 →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (∫ x, (rawAnnularCount (r/2) (3*r) x)^2 ∂graphRawLaw F) ≤ C*r^(-6:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_priced_annular_count_constant (alpha := (1/2:ℝ)) (beta := 3) (by norm_num)
  have hCn : 0 ≤ C := zero_le_one.trans hC
  refine ⟨4*C,by positivity,?_⟩
  intro Z lam N hZ hlam hN F hn hF r hr hr1
  have hψ := graphFormVector_admissible F hn
  have hm : formMass (graphFormVector F) = 1 := hψ.2.2.2.2.1
  have he : max (corePriceExcess Z lam (graphFormVector F)) 0 ≤ 1 :=
    max_le (priced_graph_tilt_excess hN F hn hF) zero_le_one
  have hb := hbound Z lam N (graphFormVector F) hψ.sobolevFermion hm hZ hlam 1 r zero_le_one hr he
  rw [rawAnnularMoment_eq_integral hψ.sobolevFermion.sobolevVector,formRawLaw_graph] at hb
  have hh := hb.trans (mul_le_mul_of_nonneg_left (annularOffsetMass_one_small hr hr1) hCn)
  simpa only [show (1/2:ℝ)*r = r/2 by ring, show C*(4*r^(-6:ℝ)) = (4*C)*r^(-6:ℝ) by ring] using hh

theorem actual_original_posterior_moment {g : Space → ℝ} (hg : Continuous g)
    (hgs : tsupport g ⊆ ball 0 1) {c₁ : ℝ} (hc : 0 < c₁)
    (hcL : c₁ < (10*(100000:ℝ))⁻¹) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ {Z lam : ℝ} {N K : ℕ}, 0 ≤ Z → 0 < lam →
      PriceMinimizes (energy Z) lam N → ∀ F : fermionGraph N,
      ‖fermionGraphValue N F‖^2 = 1 →
      formEnergy Z (graphFormVector F) ≤ energy Z N+1 →
      ∀ (ell : Fin K → ℝ) (j : ℕ) {r₀ s r : ℝ},
      0 < r₀ → 0 < s → s ≤ 1 → r₀ ≤ r → r ≤ s →
      ∀ y : Space, r ≤ ‖y‖ → ‖y‖ ≤ 2*r →
      (∫ z, (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z) y)^2
        ∂physicalObservationLaw (graphRawLaw F) K) ≤ Q*r^(-12-6*masterExponent) := by
  obtain ⟨C,hC,hcount⟩ := exists_actual_priced_moment_constant
  obtain ⟨D,hD,hpost⟩ := original_master_annular_second_moment hg hgs hc hcL
  refine ⟨D*C,mul_nonneg hD hC,?_⟩
  intro Z lam N K hZ hlam hN F hn hF ell j r₀ s r hr₀ hs hs1 hrr hrs y hy hy2
  let := graphRawLaw_probability F hn
  exact hpost (graphRawLaw F) ell j hr₀ hs hs1 hrr hrs hC
    (hcount hZ hlam hN F hn hF r (hr₀.trans_le hrr) (hrs.trans hs1)) y hy hy2

end CoulombAtom

end

end OAI
