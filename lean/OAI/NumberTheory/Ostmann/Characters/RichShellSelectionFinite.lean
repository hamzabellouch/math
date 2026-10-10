import Mathlib.Data.Finset.Sort
import OAI.NumberTheory.Ostmann.Characters.RichShellSelectionMass

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters

lemma three_separated_indices (S : Finset ℕ) (hS : 5 ≤ S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i+2 ≤ j ∧ j+2 ≤ k := by
  let e := S.orderEmbOfCardLe hS
  refine ⟨e 0,S.orderEmbOfCardLe_mem hS 0,e 2,S.orderEmbOfCardLe_mem hS 2,
    e 4,S.orderEmbOfCardLe_mem hS 4,?_,?_⟩
  · have h1 := e.strictMono (show (0 : Fin 5) < 1 by decide)
    have h2 := e.strictMono (show (1 : Fin 5) < 2 by decide)
    omega
  · have h1 := e.strictMono (show (2 : Fin 5) < 3 by decide)
    have h2 := e.strictMono (show (3 : Fin 5) < 4 by decide)
    omega

lemma five_large_weights (q : ℕ) (f : ℕ → ℝ) (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hf : ∀ i < q, f i ≤ B) (hm : q*t+4*B < ∑ i ∈ Finset.range q, f i) :
    5 ≤ ((Finset.range q).filter (fun i => t ≤ f i)).card := by
  classical
  let S := (Finset.range q).filter (fun i => t ≤ f i)
  have hs : (∑ i ∈ Finset.range q, f i) ≤ q*t + (S.card:ℝ)*B := by
    calc
      _ ≤ ∑ i ∈ Finset.range q, (t + if t ≤ f i then B else 0) := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases h : t ≤ f i
        · rw [ite_eq_left h]
          exact (hf i (Finset.mem_range.mp hi)).trans (by linarith)
        · rw [ite_eq_right h,add_zero]
          exact (lt_of_not_ge h).le
      _ = _ := by simp [Finset.sum_add_distrib,← Finset.sum_filter,S]
  by_contra h
  change ¬ 5 ≤ S.card at h
  have hc : (S.card:ℝ) ≤ 4 := by exact_mod_cast (show S.card ≤ 4 by omega)
  have := mul_le_mul_of_nonneg_right hc hB
  linarith

lemma equal_children_density_increment {M : ℕ} (f : Fin M → ℝ) (A d η : ℝ)
    (hA : d ≤ A) (hη : 0 ≤ η) (hbudget : 2*(M:ℝ)*η ≤ d)
    (hsum : ∑ i, f i = (M:ℝ)*A) (hbad : ∃ i, f i < d/2) :
    ∃ j, A+η ≤ f j := by
  classical
  obtain ⟨i,hi⟩ := hbad
  by_contra h
  push Not at h
  have hs : ∑ j ∈ (Finset.univ.erase i), f j ≤ ((M:ℝ)-1)*(A+η) := by
    calc
      _ ≤ ∑ j ∈ (Finset.univ.erase i), (A+η) :=
        Finset.sum_le_sum (fun j _ => (h j).le)
      _ = _ := by
        rw [Finset.sum_const,nsmul_eq_mul,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
        rw [Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin M)) f (Finset.mem_univ i)
  rw [hsum] at he
  nlinarith

lemma density_tree_good_node (M h : ℕ) (f : List (Fin M) → ℝ) (d η B : ℝ)
    (_hd : 0 < d) (hη : 0 ≤ η) (hbudget : 2*(M:ℝ)*η ≤ d)
    (hdepth : B < d + ((h+1:ℕ):ℝ)*η) (hroot : d ≤ f [])
    (hsum : ∀ w, w.length ≤ h → ∑ i, f (i::w) = (M:ℝ)*f w)
    (hbound : ∀ w, w.length ≤ h+1 → f w ≤ B) :
    ∃ w : List (Fin M), w.length ≤ h ∧ d ≤ f w ∧ ∀ i, d/2 ≤ f (i::w) := by
  by_contra hn
  have hbad (w : List (Fin M)) (hw : w.length ≤ h) (hdw : d ≤ f w) :
      ∃ i, f (i::w) < d/2 := by
    by_contra hh
    push Not at hh
    exact hn ⟨w,hw,hdw,hh⟩
  have hstep : ∀ l : ℕ, l ≤ h+1 → ∃ w : List (Fin M), w.length = l ∧ d+(l:ℝ)*η ≤ f w := by
    intro l
    induction l with
    | zero => intro _; exact ⟨[],rfl,by simpa using hroot⟩
    | succ l ih =>
      intro hl
      obtain ⟨w,hw,hdw⟩ := ih (by omega)
      have hwl : w.length ≤ h := by omega
      have hd0 : d ≤ f w := by nlinarith [mul_nonneg (Nat.cast_nonneg l) hη]
      obtain ⟨i,hi⟩ := equal_children_density_increment (fun i => f (i::w)) (f w) d η
        hd0 hη hbudget (hsum w hwl) (hbad w hwl hd0)
      refine ⟨i::w,by simp [hw],?_⟩
      push_cast
      linarith
  obtain ⟨w,hw,hval⟩ := hstep (h+1) le_rfl
  have := hbound w (by omega)
  linarith

end Ostmann.Characters

end

end OAI
