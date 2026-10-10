import Mathlib
import OAI.Probability.ThorpCompatibility.ClumpCost

namespace OAI

open scoped Classical
namespace ThorpCompatibility
open Finset
noncomputable def entryHeavyMass {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (a : Grid A D) : ℝ :=
  (columnPrediction Q k i (colHistory k i a)).prob
    (fun w => ¬columnLight Q H k i (colHistory k i a) w)

lemma entryHeavyMass_nonneg {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ)
    (k : Fin D) (i : Fin A) (a : Grid A D) : 0 ≤ entryHeavyMass Q H k i a :=
  Law.prob_nonneg _ _

lemma average_columnCost_lower {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (a : Grid A D) (hQa : 0 < Q.mass a) (ha : Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (k : Fin D) (i : Fin A) :
    1 - exposureError A D H K i - 2 * entryHeavyMass Q H k i a -
      (if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0) -
      (if K < (entryClumpSize k i a : ℝ) then 1 else 0) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => columnCost Q H e k i a) := by
  have hnonneg := (Law.uniform : Law (Equiv.Perm (Fin D))).mean_nonneg
    (fun e => columnCost_nonneg Q H e k i a)
  have herror := exposureError_nonneg (by omega : 1 ≤ D) hH hK i
  have ht := entryHeavyMass_nonneg Q H k i a
  have hlight : entryHeavyMass Q H k i a = 1 -
      (columnPrediction Q k i (colHistory k i a)).prob (columnLight Q H k i (colHistory k i a)) :=
    Law.prob_not _ _
  by_cases hL : 1/2 ≤ (columnPrediction Q k i (colHistory k i a)).prob
      (columnLight Q H k i (colHistory k i a))
  · by_cases haL : columnLight Q H k i (colHistory k i a) (a.2 k i)
    · by_cases hc : K < (entryClumpSize k i a : ℝ)
      · rw [ite_eq_right (not_not_intro haL), ite_eq_left hc]
        linarith
      · rw [ite_eq_right (not_not_intro haL), ite_eq_right hc]
        have hg := average_columnCost_good hD Q a hQa ha hH k i hL haL (le_of_not_gt hc)
        linarith
    · rw [ite_eq_left haL]
      have : (0 : ℝ) ≤ if K < (entryClumpSize k i a : ℝ) then 1 else 0 := by split_ifs <;> norm_num
      linarith
  · have htlarge : 1 ≤ 2 * entryHeavyMass Q H k i a := by linarith
    have h₁ : (0 : ℝ) ≤ if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0 := by
      split_ifs <;> norm_num
    have h₂ : (0 : ℝ) ≤ if K < (entryClumpSize k i a : ℝ) then 1 else 0 := by split_ifs <;> norm_num
    linarith

lemma mean_entry_heavy {A D : ℕ} (Q : Law (Grid A D)) (H : ℝ) (k : Fin D) (i : Fin A) :
    Q.mean (entryHeavyMass Q H k i) =
      Q.mean (fun a => if ¬columnLight Q H k i (colHistory k i a) (a.2 k i) then 1 else 0) := by
  have h := Q.mean_predict_prob (fun a => a.2 k i) (colHistory k i)
    (fun v w => ¬columnLight Q H k i v w)
  rw [Q.prob_eq_mean] at h
  exact h

lemma mean_columnCost_lower {A D : ℕ} (hD : 2 ≤ D) (Q : Law (Grid A D))
    (hQ : ∀ a, 0 < Q.mass a → Compatible a.1 a.2)
    {H K : ℝ} (hH : 0 ≤ H) (hK : 0 ≤ K) (k : Fin D) (i : Fin A) :
    1 - exposureError A D H K i - 3 * Q.mean (entryHeavyMass Q H k i) -
      Q.mean (fun a => if K < (entryClumpSize k i a : ℝ) then 1 else 0) ≤
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean (fun e => Q.mean (columnCost Q H e k i)) := by
  have h := Q.mean_mono_support (fun a ha =>
    average_columnCost_lower hD Q a ha (hQ a ha) hH hK k i)
  rw [Law.mean_comm] at h
  simp only [Law.mean_sub, Law.mean_const, Law.mean_const_mul] at h
  rw [← mean_entry_heavy] at h
  linarith

end ThorpCompatibility

end OAI
