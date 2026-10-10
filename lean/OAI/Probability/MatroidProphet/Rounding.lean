import OAI.Probability.MatroidProphet.Information
import OAI.Probability.MatroidProphet.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace OAI

namespace MatroidProphet
open MeasureTheory

instance levelMeasurableSpace : MeasurableSpace (Option ℤ) := ⊤
instance levelMeasurableSingletonClass : MeasurableSingletonClass (Option ℤ) :=
  ⟨fun _ => trivial⟩

noncomputable def roundedLevel (B x : ℝ) : Option ℤ :=
  if 0 < x then some ⌊Real.logb B x⌋ else none

noncomputable def levelWeight (B : ℝ) : Option ℤ → ℝ
  | none => 0
  | some i => B ^ i

noncomputable def roundedWeight (B x : ℝ) : ℝ := levelWeight B (roundedLevel B x)

theorem measurable_roundedLevel (B : ℝ) : Measurable (roundedLevel B) := by
  unfold roundedLevel
  apply Measurable.ite (measurableSet_lt measurable_const measurable_id)
  · exact (measurable_of_countable (some : ℤ → Option ℤ)).comp
      (Int.measurable_floor.comp (Real.measurable_log.div_const _))
  · exact measurable_const

lemma roundedWeight_nonneg {B : ℝ} (hB : 0 < B) (x : ℝ) :
    0 ≤ roundedWeight B x := by
  unfold roundedWeight roundedLevel
  split_ifs <;> simp only [levelWeight]
  · exact (zpow_pos hB _).le
  · exact le_rfl

lemma roundedWeight_le {B : ℝ} (hB : 1 < B) {x : ℝ} (hx : 0 ≤ x) :
    roundedWeight B x ≤ x := by
  by_cases hpos : 0 < x
  · unfold roundedWeight roundedLevel
    rw [ite_eq_left hpos, levelWeight]
    have h := (Real.le_logb_iff_rpow_le hB hpos).mp (Int.floor_le (Real.logb B x))
    simpa only [Real.rpow_intCast] using h
  · have hz : x = 0 := le_antisymm (le_of_not_gt hpos) hx
    simp [hz, roundedWeight, roundedLevel, levelWeight]

lemma le_base_mul_roundedWeight {B : ℝ} (hB : 1 < B) {x : ℝ} (hx : 0 ≤ x) :
    x ≤ B * roundedWeight B x := by
  by_cases hpos : 0 < x
  · unfold roundedWeight roundedLevel
    rw [ite_eq_left hpos, levelWeight]
    have h := (Real.logb_lt_iff_lt_rpow hB hpos).mp (Int.lt_floor_add_one (Real.logb B x))
    rw [← Int.cast_one, ← Int.cast_add, Real.rpow_intCast,
      zpow_add_one₀ (ne_of_gt (zero_lt_one.trans hB))] at h
    simpa only [mul_comm] using h.le
  · have hz : x = 0 := le_antisymm (le_of_not_gt hpos) hx
    simp [hz, roundedWeight, roundedLevel, levelWeight]

noncomputable def discreteOnlineRule {K : Type*} [Countable K] [MeasurableSpace K]
    [MeasurableSingletonClass K] {n bits : ℕ}
    (key : ℝ → K) (hkey : Measurable key)
    (choose : (k : Fin n) → Seed bits → (Fin n → K) →
      (Fin (k.val + 1) → Fin n × K) → Bool) : OnlineRule n bits where
  decide k r s hist := choose k r (fun e => key (s e))
    (fun j => ((hist j).1, key (hist j).2))
  measurable_decide k := by
    have hc : Measurable (fun x : Seed bits × ((Fin n → K) ×
        (Fin (k.val + 1) → Fin n × K)) => choose k x.1 x.2.1 x.2.2) :=
      measurable_of_countable _
    have hs : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun e => key (x.2.1 e)) := by
      apply Measurable.of_eval
      intro e
      exact hkey.comp ((measurable_pi_apply e).comp (measurable_fst.comp measurable_snd))
    have hh : Measurable (fun x : Seed bits × (Weights n × History n k) =>
        fun j => ((x.2.2 j).1, key (x.2.2 j).2)) := by
      apply Measurable.of_eval
      intro j
      have hj : Measurable (fun x : Seed bits × (Weights n × History n k) => x.2.2 j) :=
        (measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)
      exact (measurable_fst.comp hj).prodMk (hkey.comp (measurable_snd.comp hj))
    exact hc.comp (measurable_fst.prodMk (hs.prodMk hh))

lemma optimum_le_of_independent_bound {n : ℕ} (M : Matroid (Fin n)) (w : Weights n)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ I : Finset (Fin n), M.Indep (I : Set (Fin n)) → (∑ e ∈ I, w e) ≤ c) :
    optimum M w ≤ c := by
  classical
  apply Finset.sup'_le
  intro I hI
  by_cases hi : M.Indep (I : Set (Fin n))
  · simpa only [ite_eq_left hi] using hbound I hi
  · simpa only [ite_eq_right hi] using hc

theorem optimum_mono {n : ℕ} (M : Matroid (Fin n)) (v w : Weights n)
    (hvw : ∀ e, v e ≤ w e) : optimum M v ≤ optimum M w := by
  apply optimum_le_of_independent_bound M v _ (optimum_nonneg M w)
  intro I hI
  exact (Finset.sum_le_sum (fun e _ => hvw e)).trans (sum_le_optimum M w I hI)

theorem optimum_rounding_bound {n : ℕ} (M : Matroid (Fin n)) (B : ℝ) (hB : 1 < B)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) :
    optimum M w ≤ B * optimum M (fun e => roundedWeight B (w e)) := by
  apply optimum_le_of_independent_bound M w _
    (mul_nonneg (zero_lt_one.trans hB).le (optimum_nonneg M _))
  intro I hI
  calc
    (∑ e ∈ I, w e) ≤ ∑ e ∈ I, B * roundedWeight B (w e) :=
      Finset.sum_le_sum (fun e _ => le_base_mul_roundedWeight hB (hw e))
    _ = B * ∑ e ∈ I, roundedWeight B (w e) := (Finset.mul_sum ..).symm
    _ ≤ B * optimum M (fun e => roundedWeight B (w e)) :=
      mul_le_mul_of_nonneg_left (sum_le_optimum M _ I hI) (zero_lt_one.trans hB).le

end MatroidProphet

end OAI
