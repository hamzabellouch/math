import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

namespace OAI

namespace Balanced.ForwardDependencyExtraction

open Finset

theorem exists_forward_coloring {n k : ℕ} (R : Fin n → Fin n → Prop) [DecidableRel R]
    (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ k) :
    ∃ c : Fin n → Fin (k + 1),
      ∀ i j, R i j → c i = c j → i < j := by
  classical
  have aux : ∀ m : ℕ, m ≤ n →
      ∃ c : Fin n → Fin (k + 1),
        ∀ i j, i.val < m → j.val < m → R i j → c i = c j → i < j := by
    intro m
    induction m with
    | zero =>
        intro _
        exact ⟨fun _ => 0, by simp⟩
    | succ m ih =>
        intro hm
        obtain ⟨c, hc⟩ := ih (by omega)
        let v : Fin n := ⟨m, by omega⟩
        let earlier : Finset (Fin n) :=
          Finset.univ.filter (fun j => j.val < m ∧ R v j)
        have hearlier : earlier.card ≤ k := by
          calc
            earlier.card ≤ (Finset.univ.filter (R v)).card := by
              apply Finset.card_le_card
              intro j hj
              simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
              exact hj.2
            _ ≤ k := hdegree v
        have hcolors : (earlier.image c).card <
            (Finset.univ : Finset (Fin (k + 1))).card := by
          simpa using (lt_of_le_of_lt (Finset.card_image_le.trans hearlier)
            (Nat.lt_succ_self k))
        obtain ⟨color, _, hcolor⟩ :=
          Finset.exists_mem_notMem_of_card_lt_card hcolors
        refine ⟨Function.update c v color, ?_⟩
        intro i j hi hj hij heq
        by_cases hiv : i = v
        · subst i
          by_cases hjv : j = v
          · subst j
            exact False.elim (hloop v hij)
          · have hjm : j.val < m := by
              have hne : j.val ≠ m := by
                intro h
                apply hjv
                exact Fin.ext h
              omega
            have hjearlier : j ∈ earlier := by
              simp only [earlier, Finset.mem_filter, Finset.mem_univ, true_and]
              exact ⟨hjm, hij⟩
            have hchosen : color = c j := by
              simpa [Function.update, hjv] using heq
            exact False.elim (hcolor (hchosen ▸ Finset.mem_image_of_mem c hjearlier))
        · by_cases hjv : j = v
          · subst j
            have him : i.val < m := by
              have hne : i.val ≠ m := by
                intro h
                apply hiv
                exact Fin.ext h
              omega
            exact him
          · have him : i.val < m := by
              have hne : i.val ≠ m := by
                intro h
                apply hiv
                exact Fin.ext h
              omega
            have hjm : j.val < m := by
              have hne : j.val ≠ m := by
                intro h
                apply hjv
                exact Fin.ext h
              omega
            apply hc i j him hjm hij
            simpa [Function.update, hiv, hjv] using heq
  obtain ⟨c, hc⟩ := aux n le_rfl
  exact ⟨c, fun i j => hc i j i.isLt j.isLt⟩

theorem exists_forward_subset {n k t : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ k)
    (hsize : (k + 1) * (t - 1) < n) :
    ∃ s : Finset (Fin n), t ≤ s.card ∧
      ∀ i ∈ s, ∀ j ∈ s, R i j → i < j := by
  classical
  obtain ⟨c, hc⟩ := exists_forward_coloring R hloop hdegree
  obtain ⟨color, hcolor⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card c (by simpa using hsize)
  refine ⟨Finset.univ.filter (fun i => c i = color), by omega, ?_⟩
  intro i hi j hj hij
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact hc i j hij (hi.trans hj.symm)

theorem exists_large_forward_subset {n k : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ k) :
    ∃ s : Finset (Fin n), (n + k) / (k + 1) ≤ s.card ∧
      ∀ i ∈ s, ∀ j ∈ s, R i j → i < j := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨∅, ?_, by simp⟩
    simp only [Finset.card_empty, zero_add, Nat.le_zero]
    exact Nat.div_eq_of_lt (Nat.lt_succ_self k)
  · let t := (n - 1) / (k + 1) + 1
    have ht : (k + 1) * (t - 1) < n := by
      calc
        (k + 1) * (t - 1) = (k + 1) * ((n - 1) / (k + 1)) := by
          simp [t]
        _ ≤ n - 1 := Nat.mul_div_le _ _
        _ < n := by omega
    obtain ⟨s, hs, hforward⟩ := exists_forward_subset R hloop hdegree ht
    refine ⟨s, ?_, hforward⟩
    have hnlt : n - 1 < t * (k + 1) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ k)).mp
      exact Nat.lt_succ_self _
    have hnle : n ≤ (k + 1) * s.card := by
      have hnt : n ≤ t * (k + 1) := by omega
      exact hnt.trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left (k + 1) hs)
    have hceil : n + k < (s.card + 1) * (k + 1) := by nlinarith
    have hdiv := (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ k)).mpr hceil
    exact Nat.le_of_lt_succ hdiv

theorem wellFounded_on_of_forward {n : ℕ} (R : Fin n → Fin n → Prop)
    (s : Finset (Fin n))
    (hforward : ∀ i ∈ s, ∀ j ∈ s, R i j → i < j) :
    WellFounded (fun i j : {x // x ∈ s} => R i.val j.val) := by
  apply (measure (fun i : {x // x ∈ s} => i.val.val)).wf.mono
  intro i j hij
  exact hforward i.val i.property j.val j.property hij

theorem extract_three_of_eight {n : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ 2) (hn : 8 ≤ n) :
    ∃ s : Finset (Fin n), s.card = 3 ∧
      WellFounded (fun i j : {x // x ∈ s} => R i.val j.val) := by
  classical
  obtain ⟨s, hs, hf⟩ := exists_forward_subset (t := 3) R hloop hdegree (by omega)
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  refine ⟨t, ht, wellFounded_on_of_forward R t ?_⟩
  intro i hi j hj hij
  exact hf i (hts hi) j (hts hj) hij

theorem extract_two_of_four {n : ℕ} (R : Fin n → Fin n → Prop)
    [DecidableRel R] (hloop : ∀ i, ¬ R i i)
    (hdegree : ∀ i, (Finset.univ.filter (R i)).card ≤ 2) (hn : 4 ≤ n) :
    ∃ s : Finset (Fin n), s.card = 2 ∧
      WellFounded (fun i j : {x // x ∈ s} => R i.val j.val) := by
  classical
  obtain ⟨s, hs, hf⟩ := exists_forward_subset (t := 2) R hloop hdegree (by omega)
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hs
  refine ⟨t, ht, wellFounded_on_of_forward R t ?_⟩
  intro i hi j hj hij
  exact hf i (hts hi) j (hts hj) hij

end Balanced.ForwardDependencyExtraction

end OAI
