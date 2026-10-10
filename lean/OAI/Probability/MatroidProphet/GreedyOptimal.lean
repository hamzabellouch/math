import OAI.Probability.MatroidProphet.Candidates
import OAI.Probability.MatroidProphet.Density.Basic
import Mathlib.Algebra.BigOperators.Module

namespace OAI

namespace MatroidProphet
namespace Candidates

open Finset Set

variable {n : ℕ}

noncomputable def prefixCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ((I.filter fun e => time e < k).card : ℝ)

noncomputable def timeCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) : ℝ :=
  ∑ e ∈ I, if time e = k then 1 else 0

lemma sum_timeCount (time : Fin n → ℕ) (I : Finset (Fin n)) (k : ℕ) :
    (∑ i ∈ range k, timeCount time I i) = prefixCount time I k := by
  classical
  unfold timeCount prefixCount
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, ← Finset.sum_filter]
  simp

lemma sum_weight_timeCount (time : Fin n → ℕ) (ht : ∀ e, time e < n)
    (I : Finset (Fin n)) (a : ℕ → ℝ) :
    (∑ i ∈ range n, a i * timeCount time I i) = ∑ e ∈ I, a (time e) := by
  classical
  unfold timeCount
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp [mul_ite, ht e]

lemma sum_weight_le_of_prefixCount (time : Fin n → ℕ) (ht : ∀ e, time e < n)
    (I J : Finset (Fin n)) (a : ℕ → ℝ)
    (ha : ∀ i < n - 1, a (i + 1) ≤ a i) (hzero : 0 ≤ a (n - 1))
    (hprefix : ∀ k ≤ n, prefixCount time I k ≤ prefixCount time J k) :
    (∑ e ∈ I, a (time e)) ≤ ∑ e ∈ J, a (time e) := by
  rw [← sum_weight_timeCount time ht I a, ← sum_weight_timeCount time ht J a]
  have hi := Finset.sum_range_by_parts a (timeCount time I) n
  have hj := Finset.sum_range_by_parts a (timeCount time J) n
  simp only [smul_eq_mul, sum_timeCount] at hi hj
  rw [hi, hj]
  apply sub_le_sub
  · exact mul_le_mul_of_nonneg_left (hprefix n le_rfl) hzero
  · apply Finset.sum_le_sum
    intro i hi
    have hin : i < n - 1 := Finset.mem_range.mp hi
    exact mul_le_mul_of_nonpos_left (hprefix (i + 1) (by omega)) (sub_nonpos.mpr (ha i hin))

lemma greedy_univ_prefix_closure (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (time : Fin n → ℕ) (k : ℕ) :
    M.closure {e | time e < k} =
      M.closure {e | e ∈ greedy M time Finset.univ ∧ time e < k} := by
  classical
  have h := Pivots.greedy_prefix_closure M (fun e : Fin n => e) time
    (fun _ => by simp [hE]) k
  simpa [Pivots.keptOccurrences, greedy, prior] using h

lemma prefixCount_le_greedy (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (time : Fin n → ℕ) (ht : Function.Injective time)
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) (k : ℕ) :
    prefixCount time I k ≤ prefixCount time (greedy M time Finset.univ) k := by
  classical
  let G := greedy M time Finset.univ
  let IP := I.filter fun e => time e < k
  let GP := G.filter fun e => time e < k
  have hi : M.Indep (IP : Set (Fin n)) := hI.subset (by
    intro e he
    exact (Finset.mem_filter.mp he).1)
  have hg : M.Indep (GP : Set (Fin n)) :=
    (greedy_indep M time ht Finset.univ (fun _ _ => by simp [hE])).subset (by
      intro e he
      exact (Finset.mem_filter.mp he).1)
  have hsub : (IP : Set (Fin n)) ⊆ M.closure (GP : Set (Fin n)) := by
    intro e he
    have he' := (Finset.mem_filter.mp he).2
    have hc : e ∈ M.closure {e | time e < k} :=
      M.mem_closure_of_mem he' (by simp [hE])
    rw [greedy_univ_prefix_closure M hE time k] at hc
    simpa [GP, G] using hc
  have hcard : (IP : Set (Fin n)).encard ≤ (GP : Set (Fin n)).encard := by
    calc
      _ = M.eRk (IP : Set (Fin n)) := hi.eRk_eq_encard.symm
      _ ≤ M.eRk (M.closure (GP : Set (Fin n))) := M.eRk_mono hsub
      _ = M.eRk (GP : Set (Fin n)) := M.eRk_closure_eq _
      _ = _ := hg.eRk_eq_encard
  have hcNat : IP.card ≤ GP.card := by exact_mod_cast hcard
  change (IP.card : ℝ) ≤ (GP.card : ℝ)
  exact_mod_cast hcNat

noncomputable def orderedWeights (w : Weights n) (order : ArrivalOrder n) (i : ℕ) : ℝ :=
  if hi : i < n then w (order ⟨i, hi⟩) else 0

def priorityTime (order : ArrivalOrder n) (e : Fin n) : ℕ := (order.symm e).val

lemma priorityTime_injective (order : ArrivalOrder n) : Function.Injective (priorityTime order) := by
  intro a b h
  exact order.symm.injective (Fin.ext h)

@[simp] lemma orderedWeights_priorityTime (w : Weights n) (order : ArrivalOrder n) (e : Fin n) :
    orderedWeights w order (priorityTime order e) = w e := by
  simp [orderedWeights, priorityTime]

lemma greedy_dominates_independent (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (order : ArrivalOrder n)
    (hsorted : Antitone (fun i : Fin n => w (order i)))
    (I : Finset (Fin n)) (hI : M.Indep (I : Set (Fin n))) :
    (∑ e ∈ I, w e) ≤ ∑ e ∈ greedy M (priorityTime order) Finset.univ, w e := by
  have ha : ∀ i < n - 1, orderedWeights w order (i + 1) ≤ orderedWeights w order i := by
    intro i hi
    have hi' : i < n := by omega
    have his : i + 1 < n := by omega
    simpa only [orderedWeights, dite_eq_left hi', dite_eq_left his] using
      hsorted (show (⟨i, hi'⟩ : Fin n) ≤ ⟨i + 1, his⟩ from Nat.le_succ i)
  have hn : 0 ≤ orderedWeights w order (n - 1) := by
    unfold orderedWeights
    split_ifs with h
    · exact hw _
    · exact le_rfl
  have h := sum_weight_le_of_prefixCount (priorityTime order) (fun e => (order.symm e).isLt)
    I (greedy M (priorityTime order) Finset.univ) (orderedWeights w order) ha hn
    (fun k _ => prefixCount_le_greedy M hE _ (priorityTime_injective order) I hI k)
  simpa only [orderedWeights_priorityTime] using h

theorem greedy_weight_eq_optimum (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n) (hw : ∀ e, 0 ≤ w e) (order : ArrivalOrder n)
    (hsorted : Antitone (fun i : Fin n => w (order i))) :
    (∑ e ∈ greedy M (priorityTime order) Finset.univ, w e) = optimum M w := by
  classical
  apply le_antisymm
  · exact sum_le_optimum M w _ (greedy_indep M _ (priorityTime_injective order)
      Finset.univ (fun _ _ => by simp [hE]))
  · unfold optimum
    apply Finset.sup'_le
    intro I _
    split_ifs with hi
    · exact greedy_dominates_independent M hE w hw order hsorted I hi
    · exact Finset.sum_nonneg fun e _ => hw e

end Candidates
end MatroidProphet

end OAI
