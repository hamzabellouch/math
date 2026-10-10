import Mathlib
import OAI.Probability.ThorpCompatibility.PermutationCount
import OAI.Probability.ThorpCompatibility.Entropy
import OAI.Probability.ThorpCompatibility.Prediction

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α : Type*} [Fintype α] [Nonempty α]

lemma uniform_prob_card (S : α → Prop) [DecidablePred S] :
    (uniform : Law α).prob S =
      ((Finset.univ.filter S).card : ℝ) / Fintype.card α := by
  calc
    _ = ∑ _a ∈ Finset.univ.filter S, (1 / (Fintype.card α : ℝ)) := by
      rw [Finset.sum_filter]
      unfold prob uniform
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : S a <;> simp [ha]
    _ = _ := by simp [div_eq_mul_inv]

omit [Nonempty α] in
lemma restrict_prob (P : Law α) (S T : α → Prop) (hS : 0 < P.prob S) :
    (P.restrict S).prob T = P.prob (fun a => S a ∧ T a) / P.prob S := by
  simp only [prob, P.restrict_mass S hS, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : S a <;> by_cases ht : T a <;> simp [hs, ht]

end Law
open Finset

lemma uniform_rank_prob {D : ℕ} (k t : Fin D) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) = 1 / (D : ℝ) := by
  rw [Law.uniform_prob_card]
  have hc := prescribed_permutation_card {k} (Equiv.swap k t)
  simp only [Finset.mem_singleton, forall_eq, Equiv.swap_apply_left,
    Fintype.card_fin, Finset.card_singleton] at hc
  have he : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) => e k = t)).card =
      (D - 1).factorial := by convert hc using 2
  rw [he, Fintype.card_perm, Fintype.card_fin]
  have hD : 0 < D := k.pos
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  simp only [Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hd : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  simp

lemma uniform_two_rank_prob_le {D : ℕ} (hD : 2 ≤ D) (k l t s : Fin D) (hkl : k ≠ l) :
    (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t ∧ e l = s) ≤
      1 / ((D : ℝ) * (D - 1 : ℕ)) := by
  rw [Law.uniform_prob_card]
  have hc := prescribed_function_card_le {k,l} (fun x : Fin D => if x = k then t else s)
  have hs : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) =>
      ∀ x ∈ ({k,l} : Finset (Fin D)), e x = if x = k then t else s)) =
      Finset.univ.filter (fun e => e k = t ∧ e l = s) := by
    ext e
    simp [Ne.symm hkl]
  have hc' : (Finset.univ.filter (fun e : Equiv.Perm (Fin D) => e k = t ∧ e l = s)).card ≤
      (D - 2).factorial := by
    convert hc using 2
    · ext e
      simp [Ne.symm hkl]
    · simp [hkl]
  have hp : (0 : ℝ) < D.factorial := by positivity
  rw [Fintype.card_perm, Fintype.card_fin]
  calc
    _ ≤ ((D - 2).factorial : ℝ) / D.factorial :=
      div_le_div_of_nonneg_right (by exact_mod_cast hc') hp.le
    _ = _ := by
      have hf' : ((D-2).factorial : ℝ) * ((D:ℝ) * (D-1:ℕ)) = D.factorial := by
        exact_mod_cast (by simpa [Nat.descFactorial_succ, mul_comm] using
          Nat.factorial_mul_descFactorial hD)
      have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
      have hD1 : (0 : ℝ) < (D-1:ℕ) := by exact_mod_cast (by omega : 0 < D-1)
      apply (div_eq_div_iff hp.ne' (mul_pos hD0 hD1).ne').mpr
      simpa using hf'

noncomputable def rankLaw {D : ℕ} (k t : Fin D) : Law (Equiv.Perm (Fin D)) :=
  Law.uniform.restrict (fun e => e k = t)

lemma rankLaw_mass_pos_iff {D : ℕ} (k t : Fin D) (e : Equiv.Perm (Fin D)) :
    0 < (rankLaw k t).mass e ↔ e k = t := by
  have hD : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin D)) := by positivity
  have hp : 0 < (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) := by
    rw [uniform_rank_prob]; positivity
  rw [rankLaw, Law.restrict_mass _ _ hp, uniform_rank_prob]
  by_cases he : e k = t <;> simp [he, Law.uniform, hD, hc]

lemma rankLaw_other_prob_le {D : ℕ} (hD : 2 ≤ D) (k l t s : Fin D) (hkl : k ≠ l) :
    (rankLaw k t).prob (fun e => e l = s) ≤ 1 / (D - 1 : ℕ) := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast k.pos
  have hp : 0 < (Law.uniform : Law (Equiv.Perm (Fin D))).prob (fun e => e k = t) := by
    rw [uniform_rank_prob]; positivity
  rw [rankLaw, Law.restrict_prob _ _ _ hp, uniform_rank_prob]
  calc
    _ ≤ (1 / ((D : ℝ) * (D - 1 : ℕ))) / (1 / (D : ℝ)) :=
      div_le_div_of_nonneg_right (uniform_two_rank_prob_le hD k l t s hkl) (by positivity)
    _ = _ := by field_simp

end ThorpCompatibility

end OAI
