import Mathlib
import OAI.Probability.ThorpCompatibility.FiniteLaw
import OAI.Probability.ThorpCompatibility.ConditionalEntropy

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

noncomputable def prob (P : Law α) (S : α → Prop) : ℝ :=
  ∑ a, if S a then P.mass a else 0

lemma prob_nonneg (P : Law α) (S : α → Prop) : 0 ≤ P.prob S := by
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp_all [P.nonneg]

lemma prob_le_one (P : Law α) (S : α → Prop) : P.prob S ≤ 1 := by
  rw [← P.total]
  exact Finset.sum_le_sum fun a _ => by split_ifs <;> simp_all [P.nonneg]

lemma prob_mono (P : Law α) {S T : α → Prop} (h : ∀ a, S a → T a) :
    P.prob S ≤ P.prob T := by
  apply Finset.sum_le_sum
  intro a _
  by_cases hs : S a
  · simp [hs, h a hs]
  · simp [hs]
    split_ifs <;> simp_all [P.nonneg]

lemma mass_le_prob (P : Law α) (S : α → Prop) {a : α} (ha : S a) :
    P.mass a ≤ P.prob S := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun b => if S b then P.mass b else 0)
    (fun b _ => by split_ifs <;> simp_all [P.nonneg]) (Finset.mem_univ a)
  simpa [ha, prob] using h

lemma prob_not (P : Law α) (S : α → Prop) : P.prob (fun a => ¬S a) = 1 - P.prob S := by
  have h : P.prob (fun a => ¬S a) + P.prob S = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← P.total]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : S a <;> simp [ha]
  linarith

lemma prob_eq_mean (P : Law α) (S : α → Prop) [DecidablePred S] :
    P.prob S = P.mean (fun a => if S a then 1 else 0) := by
  unfold prob mean
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

noncomputable def lightRescale (P : Law α) (L S : α → Prop) : Law α :=
  if h : 0 < P.prob (fun a => L a ∧ S a) then {
    mass := fun a => (if L a ∧ S a then P.mass a else 0) *
      (P.prob L / P.prob (fun b => L b ∧ S b)) + (if ¬L a then P.mass a else 0)
    nonneg := fun a => add_nonneg
      (mul_nonneg (by split_ifs <;> simp_all [P.nonneg])
        (div_nonneg (P.prob_nonneg L) h.le))
      (by split_ifs <;> simp_all [P.nonneg])
    total := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have ha : (∑ a, if L a ∧ S a then P.mass a else 0) = P.prob (fun a => L a ∧ S a) := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : L a ∧ S a <;> simp [ha]
      have hb : (∑ a, if ¬L a then P.mass a else 0) = P.prob (fun a => ¬L a) := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : L a <;> simp [ha]
      rw [ha, hb, P.prob_not L]
      field_simp
      ring
  } else P

lemma lightRescale_mass_of_not (P : Law α) (L S : α → Prop) {a : α} (ha : ¬L a) :
    (P.lightRescale L S).mass a = P.mass a := by
  unfold lightRescale
  split_ifs <;> simp [ha]

lemma lightRescale_mass_of_mem (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hL : L a) (hS : S a) :
    (P.lightRescale L S).mass a = P.mass a * P.prob L / P.prob (fun a => L a ∧ S a) := by
  have hA : 0 < P.prob (fun a => L a ∧ S a) :=
    lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩)
  simp [lightRescale, hA, hL, hS, mul_div_assoc]

lemma lightRescale_pos (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hS : S a) : 0 < (P.lightRescale L S).mass a := by
  by_cases hL : L a
  · rw [P.lightRescale_mass_of_mem L S hp hL hS]
    exact div_pos (mul_pos hp (lt_of_lt_of_le hp (P.mass_le_prob L hL)))
      (lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩))
  · simpa [P.lightRescale_mass_of_not L S hL] using hp

lemma lightRescale_log (P : Law α) (L S : α → Prop) {a : α}
    (hp : 0 < P.mass a) (hS : S a) :
    Real.log ((P.lightRescale L S).mass a) = Real.log (P.mass a) -
      (if L a then Real.log (P.prob (fun b => L b ∧ S b) / P.prob L) else 0) := by
  by_cases hL : L a
  · have hA : 0 < P.prob (fun b => L b ∧ S b) :=
      lt_of_lt_of_le hp (P.mass_le_prob _ ⟨hL, hS⟩)
    have hB : 0 < P.prob L := lt_of_lt_of_le hp (P.mass_le_prob L hL)
    rw [P.lightRescale_mass_of_mem L S hp hL hS, ite_eq_left hL,
      Real.log_div (mul_pos hp hB).ne' hA.ne', Real.log_mul hp.ne' hB.ne',
      Real.log_div hA.ne' hB.ne']
    ring
  · rw [P.lightRescale_mass_of_not L S hL, ite_eq_right hL, sub_zero]

lemma light_cost_nonneg (P : Law α) (L S : α → Prop) :
    0 ≤ -Real.log (P.prob (fun b => L b ∧ S b) / P.prob L) := by
  apply neg_nonneg.mpr
  apply Real.log_nonpos (div_nonneg (P.prob_nonneg _) (P.prob_nonneg _))
  by_cases hL : P.prob L = 0
  · simp [hL]
  · exact (div_le_one (lt_of_le_of_ne (P.prob_nonneg _) (Ne.symm hL))).mpr
      (P.prob_mono fun _ h => h.1)

lemma condEntropy_light_comparison (P : Law α) (X : α → β) (Y : α → γ)
    (K : γ → Law β) (L S : γ → β → Prop)
    (hK : ∀ a, 0 < P.mass a → 0 < (K (Y a)).mass (X a))
    (hS : ∀ a, 0 < P.mass a → S (Y a) (X a)) :
    P.mean (fun a => if L (Y a) (X a) then
      -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
        (K (Y a)).prob (L (Y a))) else 0) ≤
      -P.mean (fun a => Real.log ((K (Y a)).mass (X a))) - P.condEntropy X Y := by
  have h := P.condEntropy_le_prediction X Y
    (fun y => (K y).lightRescale (L y) (S y))
    (fun a ha => (K (Y a)).lightRescale_pos (L (Y a)) (S (Y a)) (hK a ha) (hS a ha))
  have he : P.mean (fun a => Real.log (((K (Y a)).lightRescale (L (Y a)) (S (Y a))).mass (X a))) =
      P.mean (fun a => Real.log ((K (Y a)).mass (X a))) +
        P.mean (fun a => if L (Y a) (X a) then
          -Real.log ((K (Y a)).prob (fun b => L (Y a) b ∧ S (Y a) b) /
            (K (Y a)).prob (L (Y a))) else 0) := by
    rw [← P.mean_add]
    apply P.mean_congr_support
    intro a ha
    rw [(K (Y a)).lightRescale_log _ _ (hK a ha) (hS a ha)]
    split_ifs <;> ring
  rw [he] at h
  linarith

end Law
end ThorpCompatibility

end OAI
