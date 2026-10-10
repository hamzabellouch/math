import Mathlib
import OAI.Probability.ThorpCompatibility.RankLaw

namespace OAI

open scoped Classical
namespace ThorpCompatibility
namespace Law
open Finset
variable {α β : Type*} [Fintype α] [Fintype β]

lemma mean_comm (P : Law α) (Q : Law β) (f : α → β → ℝ) :
    P.mean (fun a => Q.mean (f a)) = Q.mean (fun b => P.mean (fun a => f a b)) := by
  simp only [mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma prob_congr_support (P : Law α) {S T : α → Prop}
    (h : ∀ a, 0 < P.mass a → (S a ↔ T a)) : P.prob S = P.prob T := by
  rw [P.prob_eq_mean, P.prob_eq_mean]
  apply P.mean_congr_support
  intro a ha
  rw [h a ha]

lemma prob_map (P : Law α) (f : α → β) (S : β → Prop) :
    (P.map f).prob S = P.prob (fun a => S (f a)) := by
  rw [P.prob_eq_mean, prob_eq_mean, P.mean_map]
  rfl

lemma prob_eq_sum_filter (P : Law α) (S : α → Prop) [DecidablePred S] :
    P.prob S = ∑ a ∈ Finset.univ.filter S, P.mass a := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

lemma prob_le_card_mul (P : Law α) (S : α → Prop) [DecidablePred S]
    (c : ℝ) (hc : ∀ a, S a → P.mass a ≤ c) :
    P.prob S ≤ ((Finset.univ.filter S).card : ℝ) * c := by
  rw [P.prob_eq_sum_filter S]
  calc
    _ ≤ ∑ _a ∈ Finset.univ.filter S, c :=
      Finset.sum_le_sum (fun a ha => hc a (Finset.mem_filter.mp ha).2)
    _ = _ := by simp

lemma mean_ite_const (P : Law α) (S : α → Prop) [DecidablePred S] (x y : ℝ) :
    P.mean (fun a => if S a then x else y) =
      P.prob S * x + (1 - P.prob S) * y := by
  rw [← P.prob_not S]
  simp only [mean, prob, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : S a <;> simp [ha]

end Law
open Finset

lemma rankLaw_mean_average {D : ℕ} (k : Fin D) (g : Equiv.Perm (Fin D) → ℝ) :
    (∑ t, (rankLaw k t).mean g) / (D : ℝ) =
      (Law.uniform : Law (Equiv.Perm (Fin D))).mean g := by
  let P : Law (Equiv.Perm (Fin D)) := Law.uniform
  have h := P.mean_predict id (fun e => e k) (fun _ e => g e)
  have he : P.mean (fun e => (P.predict id (fun e => e k) (e k)).mean g) =
      (P.map (fun e => e k)).mean (fun t => (rankLaw k t).mean g) := by
    rw [P.mean_map]
    simp only [Law.predict, Law.map_id, rankLaw, P]
    rfl
  rw [he] at h
  have hm (t : Fin D) : (P.map (fun e => e k)).mass t = 1 / (D : ℝ) := by
    rw [← P.prob_eq_map_mass]
    exact uniform_rank_prob k t
  simpa only [Law.mean, hm, id_eq, one_div, ← Finset.mul_sum, div_eq_mul_inv,
    mul_comm, mul_one, P] using h

lemma rankLaw_later_le {D : ℕ} (hD : 2 ≤ D) (k l t : Fin D) (hkl : k ≠ l) :
    (rankLaw k t).prob (fun e => e k ≤ e l) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) := by
  have he : (rankLaw k t).prob (fun e => e k ≤ e l) =
      ((rankLaw k t).map (fun e => e l)).prob (fun s => t < s) := by
    rw [Law.prob_map]
    apply Law.prob_congr_support
    intro e he
    have hk := (rankLaw_mass_pos_iff k t e).mp he
    have hn : e l ≠ e k := fun h => hkl (e.injective h).symm
    rw [hk] at hn ⊢
    constructor
    · intro h
      exact lt_of_le_of_ne h (Ne.symm hn)
    · exact le_of_lt
  rw [he]
  have hb := Law.prob_le_card_mul ((rankLaw k t).map (fun e => e l)) (fun s => t < s)
    (1 / ((D - 1 : ℕ) : ℝ)) (by
      intro s _
      rw [← Law.prob_eq_map_mass]
      exact rankLaw_other_prob_le hD k l t s hkl)
  have hc : (Finset.univ.filter (fun s : Fin D => t < s)).card = D - 1 - (t : ℕ) := by
    have he : Finset.univ.filter (fun s : Fin D => t < s) = Finset.Ioi t := by ext s; simp
    rw [he, Fin.card_Ioi]
  rw [hc] at hb
  refine le_trans hb ?_
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have ht0 : (t : ℕ) ≤ D - 1 := by omega
  have hDt : (t : ℕ) ≤ D := Nat.le_of_lt t.isLt
  have hD1 : (0 : ℝ) < (D : ℝ) - 1 := by
    have h : (1 : ℝ) < D := by exact_mod_cast (by omega : 1 < D)
    linarith
  rw [Nat.cast_sub ht0, Nat.cast_sub (by omega : 1 ≤ D), Nat.cast_sub hDt, Nat.cast_one]
  rw [mul_one_div]
  apply (div_le_div_iff₀ hD1 hD0).mpr
  have htpos : (0 : ℝ) ≤ (t : ℕ) := Nat.cast_nonneg _
  nlinarith

lemma rankLaw_allowed_mean_le {β : Type*} [Fintype β] {D : ℕ} (hD : 2 ≤ D)
    (B : Law β) (f : β → Fin D) (k t : Fin D) :
    (rankLaw k t).mean (fun e => B.prob (fun b => e k ≤ e (f b))) ≤
      ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) + B.prob (fun b => f b = k) := by
  simp_rw [Law.prob_eq_mean]
  rw [Law.mean_comm]
  have hprob (b : β) : (rankLaw k t).mean (fun e => if e k ≤ e (f b) then 1 else 0) ≤
      (if f b = k then 1 else ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ)) := by
    by_cases hb : f b = k
    · simp [hb, Law.mean_const]
    · rw [ite_eq_right hb, ← Law.prob_eq_mean]
      exact rankLaw_later_le hD k (f b) t (Ne.symm hb)
  have h := B.mean_mono hprob
  rw [B.mean_ite_const] at h
  rw [← B.prob_eq_mean]
  refine le_trans h ?_
  have hα := B.prob_nonneg (fun b => f b = k)
  have hb : 0 ≤ ((D - (t : ℕ) : ℕ) : ℝ) / (D : ℝ) := by positivity
  nlinarith

end ThorpCompatibility

end OAI
