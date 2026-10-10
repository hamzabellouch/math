import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.FreshCutBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal ENNReal

namespace CoulombAtom
open CoulombObservation CoulombNeumann CoulombAnalysis
local instance : Fact ((5/3:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance : Fact ((5/2:ℝ≥0∞) ≠ ⊤) := ⟨by finiteness⟩
local instance (R : ℝ) : MeasurableSpace (TFLp (ballMeasure R)) := borel _
local instance (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma centered_test_memLp (y : Space) (R : ℝ) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {r : ℝ} (hs : Function.support g ⊆ closedBall y r) :
    MemLp (fun z => g (y+z)) (5/2) (ballMeasure R) := by
  have hc : Continuous (fun z => g (y+z)) := hg.continuous.comp (continuous_const.add continuous_id)
  have hcs : Function.support (fun z => g (y+z)) ⊆ closedBall (0 : Space) r := by
    intro z hz
    have hh := hs hz
    simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left,sub_zero] using hh
  exact (hc.memLp_of_hasCompactSupport
    (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Space) r) hcs)).mono_measure
      Measure.restrict_le_self

def freshRadialTest {N : ℕ} (y : Space) (t : ℝ) {b : ℝ} (hb : 0 < b)
    (g : Space → ℝ) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) : ℝ :=
  ∫ z, g (y+z)*retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b) z
    ∂ballMeasure (t-4*b)

lemma freshRadialTest_measurable {N : ℕ} (y : Space) (t : ℝ) {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g) {r : ℝ}
    (hs : Function.support g ⊆ closedBall y r) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    Measurable (freshRadialTest y t hb g c s) :=
  (patch_test_continuous_of_memLp (t-4*b) (centered_test_memLp y (t-4*b) hg hs)).measurable.comp
    (retainedPatchLp_measurable hb _ id (radialPatchRetention_measurable N y t b c s) measurable_id y (t-4*b))

lemma freshRadialTest_eq_smear {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (g : Space → ℝ) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    (u : Configuration (cutOutNumber c)) :
    freshRadialTest y t hb g c s u =
      ∫ v, g v*retainedSmear b (radialPatchRetention N y t b c s u) u v := by
  exact retainedPatchLp_field hb _ _ y (radialPatch_retained_margin y hb c s u) g

theorem event_fresh_high_test_support {N K : ℕ} (F G : fermionGraph N)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) {j : ℕ} (k : Fin K) (hk : j ≤ k.val)
    (y : Space) {t b r : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (T Q : ℝ)
    (hdata : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      T+Q*((L:ℝ)*Real.sqrt 3*(b+2*ell k)) < posteriorTestValue (graphRawLaw F) ell j g z ∧
      observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z ≤ Q) :
    ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (graphFormVector G) c) s u) ≠ 0 →
      T < freshRadialTest y t hb g c s u := by
  intro c s
  have hnoise := hell k
  have hh := fresh_original_observed_sandwich (graphRawLaw F) ell hell k hk y ht hb hr hg hs
  have hp := event_fresh_cut_support F G ell _ _ c
    (P := fun u => T < freshRadialTest y t hb g c s u)
    (measurableSet_lt measurable_const (freshRadialTest_measurable y t hb hg hs c s)) hA hlaw
    (by
      filter_upwards [hh,hdata] with z hz hdatum
      intro hzA hc
      have he := (hz c hc s).trans (mul_le_mul_of_nonneg_right (hdatum hzA).2
        (by positivity : 0 ≤ (L:ℝ)*Real.sqrt 3*(b+2*ell k)))
      rw [←freshRadialTest_eq_smear y hb g c s] at he
      have he' := (abs_le.mp (by simpa only [Real.norm_eq_abs] using he)).1
      linarith [(hdatum hzA).1])
  exact hp s

theorem event_fresh_low_test_support {N K : ℕ} (F G : fermionGraph N)
    (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k) {j : ℕ} (k : Fin K) (hk : j ≤ k.val)
    (y : Space) {t b r : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hr : r < t-7*b)
    {g : Space → ℝ} {L : ℝ≥0} (hg : LipschitzWith L g)
    (hs : Function.support g ⊆ closedBall y r)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))} (hA : MeasurableSet A)
    {d : ℝ≥0∞} (hlaw : graphRawLaw G = d • Measure.map Prod.fst
      ((physicalObservationLaw (graphRawLaw F) K).restrict A))
    (T Q : ℝ)
    (hdata : ∀ᵐ z ∂physicalObservationLaw (graphRawLaw F) K, z ∈ A →
      posteriorTestValue (graphRawLaw F) ell j g z+Q*((L:ℝ)*Real.sqrt 3*(b+2*ell k)) < T ∧
      observedLocalCount ell k y (r+Real.sqrt 3*(b+ell k)) z ≤ Q) :
    ∀ c : Fin N → Fin 2, ∀ s : Spins (cutOutNumber c), ∀ᵐ u,
      formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (graphFormVector G) c) s u) ≠ 0 →
      freshRadialTest y t hb g c s u < T := by
  intro c s
  have hnoise := hell k
  have hh := fresh_original_observed_sandwich (graphRawLaw F) ell hell k hk y ht hb hr hg hs
  have hp := event_fresh_cut_support F G ell _ _ c
    (P := fun u => freshRadialTest y t hb g c s u < T)
    (measurableSet_lt (freshRadialTest_measurable y t hb hg hs c s) measurable_const) hA hlaw
    (by
      filter_upwards [hh,hdata] with z hz hdatum
      intro hzA hc
      have he := (hz c hc s).trans (mul_le_mul_of_nonneg_right (hdatum hzA).2
        (by positivity : 0 ≤ (L:ℝ)*Real.sqrt 3*(b+2*ell k)))
      rw [←freshRadialTest_eq_smear y hb g c s] at he
      have he' := (abs_le.mp (by simpa only [Real.norm_eq_abs] using he)).2
      linarith [(hdatum hzA).1])
  exact hp s

end CoulombAtom

end

end OAI
