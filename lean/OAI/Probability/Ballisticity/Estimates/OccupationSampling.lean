import Mathlib
import OAI.Probability.Ballisticity.Stationary.StationaryCompact
import OAI.Probability.Ballisticity.Estimates.SamplingLimit
import OAI.Probability.Ballisticity.Estimates.SamplingLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical
namespace DirectionalTransience

noncomputable def actualOccupationRaw {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d))
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : Measure (ActualEpisodeArray e) :=
  StationaryCompact.episodeOccupationRaw N (episodeInputLaw e ν Q t ht)
    (actualArrayMap e t J) (fun X => M X.1.1) StationaryCompact.shift

instance actualOccupationRaw_finite {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : IsFiniteMeasure (actualOccupationRaw e ν Q t J ht N M) := by
  unfold actualOccupationRaw
  infer_instance

lemma actualOccupationRaw_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M) (F : C(ActualEpisodeArray e,ℝ)) :
    (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=
      ∑ i∈Finset.range N, ∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
        ∂episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht := by
  unfold actualOccupationRaw StationaryCompact.episodeOccupationRaw
  rw [integral_finsetSum_measure (fun i _ =>
    F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply Finset.sum_congr rfl
  intro i _
  have hm : Measurable (fun X : EpisodeInput e => StationaryCompact.shift^[i] (actualArrayMap e t J X)) :=
    (StationaryCompact.shift_continuous.measurable.iterate i).comp (actualArrayMap_measurable e t J ht hJ)
  rw [integral_map hm.aemeasurable F.continuous.aestronglyMeasurable]
  have hr : (episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1}=
      episodeInputLaw e ν (Q.restrict {ω | i<M ω}) t ht :=
    episodeInputLaw_restrict e ν Q t ht {ω | i<M ω} (measurableSet_lt measurable_const hM)
  change (∫ X, F (StationaryCompact.shift^[i] (actualArrayMap e t J X))
    ∂(episodeInputLaw e ν Q t ht).restrict {X | i<M X.1.1})=_
  rw [hr]

lemma episodeInputLaw_real_univ {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i) :
    (episodeInputLaw e ν Q t ht).real Set.univ=Q.real Set.univ := by
  simp [Measure.real,episodeInputLaw,Measure.prod_apply,Measure.compProd_apply,
    measure_univ]

lemma actualOccupationRaw_mass {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M) :
    (actualOccupationRaw e ν Q t J ht N M).real Set.univ=
      ∑ i∈Finset.range N, (Q.restrict {ω | i<M ω}).real Set.univ := by
  have h := actualOccupationRaw_integral e ν Q t J ht hJ N M hM (1 : C(ActualEpisodeArray e,ℝ))
  simpa only [ContinuousMap.one_apply,integral_const,smul_eq_mul,mul_one,
    episodeInputLaw_real_univ] using h

lemma actualOccupationRaw_sampling_sq {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ Y, (arraySamplingError e p j z n Y)^2 ∂actualOccupationRaw e ν Q t J ht N M)≤
      (actualOccupationRaw e ν Q t J ht N M).real Set.univ*(n:ℝ)⁻¹ := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => (arraySamplingError e p j z n Y)^2,by fun_prop⟩
  change (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)≤_
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F,
    actualOccupationRaw_mass e ν Q t J ht hJ N M hM,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [F,ContinuousMap.coe_mk,arraySamplingError_iterate]
  exact actual_array_sampling_sq_law e ν (Q.restrict {ω | i<M ω}) t J ht hJ _ _ z n hn

lemma actualOccupationRaw_sampling_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ Y, g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y)
      ∂actualOccupationRaw e ν Q t J ht N M)=0 := by
  let F : C(ActualEpisodeArray e,ℝ) := ⟨fun Y => g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y),
      (g.continuous.comp (arrayProfileTest e q.1 p z).continuous).mul
        ((arrayOffsetTest e p q z).continuous.sub (arrayProfileTest e q.1 p z).continuous)⟩
  change (∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M)=_
  rw [actualOccupationRaw_integral e ν Q t J ht hJ N M hM F]
  apply Finset.sum_eq_zero
  intro i _
  simp only [F,ContinuousMap.coe_mk,arrayProfileTest_iterate,arrayOffsetTest_iterate]
  have hneq : (p.1+(i:ℤ),p.2)≠(q.1+(i:ℤ),q.2) := by
    intro he
    apply hpq
    apply Prod.ext
    · exact add_right_cancel (congrArg Prod.fst he)
    · have hh := congrArg (fun r : ℤ×ℕ => r.2) he
      exact hh
  exact actual_array_sampling_test_law e ν (Q.restrict {ω | i<M ω}) t J ht hJ
    (p.1+(i:ℤ),p.2) (q.1+(i:ℤ),q.2) hneq z g

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal NNReal BigOperators Classical Topology
namespace DirectionalTransience

noncomputable def actualOccupation {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ) : ProbabilityMeasure (ActualEpisodeArray e) := by
  haveI : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  exact FiniteMeasure.normalize (⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩ : FiniteMeasure (ActualEpisodeArray e))

lemma actualOccupation_integral {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ) (ht : ∀ i, Measurable fun ω => t ω i)
    (N : ℕ) (M : Environment d → ℕ)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (F : ActualEpisodeArray e → ℝ) :
    (∫ Y, F Y ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=
      ((actualOccupationRaw e ν Q t J ht N M).real Set.univ)⁻¹ *
        ∫ Y, F Y ∂actualOccupationRaw e ν Q t J ht N M := by
  have : Nonempty (Row d) := nonempty_of_isProbabilityMeasure ν
  let ρ : FiniteMeasure (ActualEpisodeArray e) := ⟨actualOccupationRaw e ν Q t J ht N M,inferInstance⟩
  have hn : ρ≠0 := by
    intro hz
    have hh : (actualOccupationRaw e ν Q t J ht N M).real Set.univ=0 := by
      change (ρ : Measure (ActualEpisodeArray e)).real Set.univ=0
      rw [hz]
      simp
    linarith
  change (∫ Y, F Y ∂(ρ.normalize : Measure (ActualEpisodeArray e)))=_
  rw [←ρ.average_eq_integral_normalize hn,average,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul]
  rfl

lemma actualOccupation_sampling_sq {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) (n : ℕ) (hn : 0<n) :
    (∫ Y, (arraySamplingError e p j z n Y)^2
      ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))≤(n:ℝ)⁻¹ := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos]
  have hb := actualOccupationRaw_sampling_sq e ν Q t J ht hJ N M hM p j z n hn
  exact (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpos.le)).trans_eq
    (by rw [←mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul])

lemma actualOccupation_sampling_test {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν] (Q : Measure (Environment d)) [IsFiniteMeasure Q]
    (t J : Environment d → ℤ → ℕ)
    (ht : ∀ i, Measurable fun ω => t ω i) (hJ : ∀ i, Measurable fun ω => J ω i)
    (N : ℕ) (M : Environment d → ℕ) (hM : Measurable M)
    (hpos : 0<(actualOccupationRaw e ν Q t J ht N M).real Set.univ)
    (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) (g : C(ℝ,ℝ)) :
    (∫ Y, g (arrayProfileTest e q.1 p z Y)*
      (arrayOffsetTest e p q z Y-arrayProfileTest e q.1 p z Y)
      ∂(actualOccupation e ν Q t J ht N M : Measure (ActualEpisodeArray e)))=0 := by
  rw [actualOccupation_integral e ν Q t J ht N M hpos,
    actualOccupationRaw_sampling_test e ν Q t J ht hJ N M hM p q hpq z g,mul_zero]

section WeakLimit
variable {d : ℕ} (e : Direction d)
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Measure (Environment d)) [∀ r, IsFiniteMeasure (Q r)]
    (t J : ℕ → Environment d → ℤ → ℕ)
    (ht : ∀ r i, Measurable fun ω => t r ω i) (hJ : ∀ r i, Measurable fun ω => J r ω i)
    (N : ℕ → ℕ) (M : ℕ → Environment d → ℕ) (hM : ∀ r, Measurable (M r))
    (hpos : ∀ r, 0<(actualOccupationRaw e ν (Q r) (t r) (J r) (ht r) (N r) (M r)).real Set.univ)
    (L : ProbabilityMeasure (ActualEpisodeArray e))
    (hlim : Tendsto (fun r => actualOccupation e ν (Q r) (t r) (J r) (ht r) (N r) (M r)) atTop (𝓝 L))

include hJ hM hpos hlim

theorem actualOccupation_limit_sampling (p : ℤ×ℕ) (j : ℤ) (z : HorizontalSpace e) :
    ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)),
      Tendsto (fun n => arraySamplingError e p j z (2^n) Y) atTop (𝓝 0) := by
  apply Sampling.ae_sampling_of_weak_limit _ L hlim (fun n => arraySamplingError e p j z (2^n))
    (fun n => ((2:ℕ)^n:ℝ)⁻¹)
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,inv_pow] using
      summable_geometric_of_norm_lt_one (x:=((2:ℝ)⁻¹)) (by norm_num)
  · intro r n
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using actualOccupation_sampling_sq e ν (Q r) (t r) (J r) (ht r) (hJ r) (N r) (M r)
      (hM r) (hpos r) p j z (2^n) (pow_pos (by norm_num) n)

theorem actualOccupation_limit_zero (p q : ℤ×ℕ) (hpq : p≠q) (z : HorizontalSpace e) :
    ∀ᵐ Y ∂(L : Measure (ActualEpisodeArray e)),
      arrayProfileTest e q.1 p z Y=0 → arrayOffsetTest e p q z Y=0 := by
  apply Sampling.ae_zero_of_sampling_tests (arrayProfileTest e q.1 p z) (arrayOffsetTest e p q z)
    (arrayProfileTest e q.1 p z).continuous.measurable (arrayOffsetTest e p q z).continuous.measurable
    (arrayProfileTest_mem e q.1 p z) (arrayOffsetTest_mem e p q z)
  apply Sampling.sampling_tests_weak_limit _ L hlim
  intro r g
  exact actualOccupation_sampling_test e ν (Q r) (t r) (J r) (ht r) (hJ r) (N r) (M r)
    (hM r) (hpos r) p q hpq z g

end WeakLimit
end DirectionalTransience

end

end OAI
