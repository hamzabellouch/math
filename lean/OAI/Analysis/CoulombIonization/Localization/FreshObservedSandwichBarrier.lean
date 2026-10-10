import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.ActualMasterCenterComparison
import OAI.Analysis.CoulombIonization.RadialBounds.CoreHistoryCountsBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FreshObservedSandwich_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

open CoulombObservation CoulombNeumann CoulombAnalysis

lemma observedLocalCount_mono {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) {r R : ℝ} (hr : r ≤ R)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) :
    observedLocalCount ell k y r z ≤ observedLocalCount ell k y R z := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · exact False.elim (hj (hi.trans hr))
  · norm_num
  · exact le_rfl

lemma cut_filtered_count_le_observed {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) (r : ℝ) (c : Fin N → Fin 2)
    (S : Finset (Fin (cutOutNumber c)))
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    ((S.filter (fun i => ‖cutOutPositions c z.1 i-y‖ ≤ r)).card:ℝ) ≤
      observedLocalCount ell k y (r+Real.sqrt 3*ell k) z := by
  classical
  let f : Fin (cutOutNumber c) → Fin N := fun i => cutOrder c (finSumFinEquiv (Sum.inr i))
  have hf : Function.Injective f := (cutOrder c).injective.comp
    (finSumFinEquiv.injective.comp Sum.inr_injective)
  have hh : (S.filter (fun i => ‖cutOutPositions c z.1 i-y‖ ≤ r)).card ≤
      (Finset.univ.filter (fun i => ‖physicalObservedConfiguration ell k z i-y‖ ≤
        r+Real.sqrt 3*ell k)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i hi
      change f i ∈ Finset.univ.filter _
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have ht := norm_add_le (physicalObservedConfiguration ell k z (f i)-z.1 (f i))
        (z.1 (f i)-y)
      rw [sub_add_sub_cancel] at ht
      exact (ht.trans (add_le_add (hd (f i)) (Finset.mem_filter.mp hi).2)).trans_eq (add_comm _ _)
    · exact fun _ _ _ _ h => hf h
  simpa only [observedLocalCount,Finset.sum_boole] using (Nat.cast_le (α := ℝ)).mpr hh

theorem fresh_original_observed_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) (y : Space) {t b r : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ (c : Fin N → Fin 2),
      (spatialProduct (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) c).value z.1 ≠ 0 →
      ∀ s : Spins (cutOutNumber c),
      let u := cutOutPositions c z.1
      let S := radialPatchRetention N y t b c s u
      ‖(∫ v, g v*retainedSmear b S u v)-posteriorTestValue μ ell j g z‖ ≤
        observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z*
          ((L:ℝ)*Real.sqrt 3*(b+2*ell k)) := by
  filter_upwards [fresh_original_posterior_sandwich μ ell hell k hk y ht hb hr hg hs,
    physicalObservationLaw_ae_displacement μ ell hell] with z hz hd
  intro c hc s
  dsimp only
  have hnoise := hell k
  have hf := cut_filtered_count_le_observed ell k y (r+Real.sqrt 3*b) c
    (radialPatchRetention N y t b c s (cutOutPositions c z.1)) z (hd k)
  have he : r+Real.sqrt 3*b+Real.sqrt 3*ell k = r+Real.sqrt 3*(b+ell k) := by ring
  rw [he] at hf
  have hm := observedLocalCount_mono ell k y
    (show r+Real.sqrt 3*ell k ≤ r+Real.sqrt 3*(b+ell k) by
      nlinarith [Real.sqrt_nonneg (3:ℝ)]) z
  have h1 := mul_le_mul_of_nonneg_right hf
    (by positivity : 0 ≤ (L:ℝ)*(Real.sqrt 3*b))
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2))
    (by positivity : 0 ≤ (L:ℝ)*(Real.sqrt 3*ell k))
  exact (hz c hc s).trans ((add_le_add h1 h2).trans_eq (by ring))

end Work_FreshObservedSandwich_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal

open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma observed_count_le_raw_enlarged {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K)
    (y : Space) {R Q : ℝ} (hRQ : R+Real.sqrt 3*ell k < Q)
    (z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))
    (hd : ∀ i, ‖physicalObservedConfiguration ell k z i-z.1 i‖ ≤ Real.sqrt 3*ell k) :
    observedLocalCount ell k y R z ≤ rawBallCount y Q z.1 := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi hj hj
  · exact le_rfl
  · have ht := norm_add_le (z.1 i-physicalObservedConfiguration ell k z i)
      (physicalObservedConfiguration ell k z i-y)
    rw [sub_add_sub_cancel] at ht
    have hd' : ‖z.1 i-physicalObservedConfiguration ell k z i‖ ≤ Real.sqrt 3*ell k := by
      simpa only [norm_sub_rev] using hd i
    exact False.elim (hj (by linarith [hd']))
  · norm_num
  · exact le_rfl

lemma event_rawLaw_ae {N K : ℕ} (F G : fermionGraph N) (_ell : Fin K → ℝ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    {P : Configuration N → Prop} (hP : MeasurableSet {x | P x})
    (hA : MeasurableSet A)
    (h : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A → P z.1) :
    ∀ᵐ x ∂graphRawLaw G, P x := by
  rw [hlaw]
  apply Measure.ae_smul_measure _ c
  exact (ae_map_iff measurable_fst.aemeasurable hP).mpr ((ae_restrict_iff' hA).mpr h)

lemma event_raw_count_lower {N K : ℕ} (F G : fermionGraph N)
    (hGn : ‖fermionGraphValue N G‖^2 = 1) (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    (k : Fin K) (y : Space) {R Q T : ℝ} (hT : 0 ≤ T)
    (hRQ : R+Real.sqrt 3*ell k < Q)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet A) (hcount : ∀ z ∈ A, T ≤ observedLocalCount ell k y R z)
    {c : ℝ≥0∞} (hlaw : graphRawLaw G = c • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A)) :
    T^2 ≤ rawCountMoment (graphFormVector G) y Q := by
  have he := event_rawLaw_ae F G ell hlaw
    (measurableSet_le measurable_const (rawBallCount_measurable y Q)) hA
    (by
      filter_upwards [physicalObservationLaw_ae_displacement (graphRawLaw F) ell hell] with z hz
      intro hzA
      exact (hcount z hzA).trans (observed_count_le_raw_enlarged ell k y hRQ z (hz k)))
  let := graphRawLaw_probability G hGn
  rw [rawCountMoment_eq_integral (graphFormVector_sobolev G).sobolevVector,formRawLaw_graph]
  calc
    T^2 = ∫ _x : Configuration N, T^2 ∂graphRawLaw G := by simp
    _ ≤ ∫ x, rawBallCount y Q x^2 ∂graphRawLaw G :=
      integral_mono_ae (integrable_const _) (rawBallCount_sq_integrable y Q _)
        (he.mono (fun x hx => pow_le_pow_left₀ hT hx 2))

end CoulombAtom

end

end OAI
