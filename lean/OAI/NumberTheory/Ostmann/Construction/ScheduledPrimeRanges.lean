import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedCompensationPrior
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialPrimeLower

namespace OAI

/-! # Live prime ranges of the selected finite schedule -/
namespace Ostmann
open scoped Classical

theorem scheduledSmallCell_property (P : ℕ → Prop) (top : ℕ) (cs : List ℕ)
    (htop : P top) (hcs : ∀ c ∈ cs, P c) :
    ∀ i, P (scheduledSmallCell top cs i) := by
  induction cs with
  | nil => exact fun _ => htop
  | cons c cs ih =>
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [scheduledSmallCell, Fin.append_left] using hcs c (by simp)
    · simpa only [scheduledSmallCell, Fin.append_right] using
        ih (fun d hd => hcs d (by simp [hd])) j

theorem mem_initialSmallCellList_of_eq_or_mem (top : ℕ) (cs : List ℕ) (j : ℕ)
    (h : j = top ∨ j ∈ cs) : j ∈ initialSmallCellList top cs := by
  rcases h with rfl | hj
  · simp [initialSmallCellList]
  · simp only [initialSmallCellList, List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨j, hj, by simp⟩

theorem completedCompensationCell_mem_initial (top : ℕ) (cs : List ℕ) (n : ℕ) :
    completedCompensationCell top cs n ∈ initialSmallCellList top cs := by
  apply mem_initialSmallCellList_of_eq_or_mem
  by_cases hn : n < cs.length
  · right
    rw [completedCompensationCell_used top cs n hn, list_headD_drop_get cs 0 n hn]
    exact List.get_mem _ _
  · left
    simp only [completedCompensationCell, List.drop_eq_nil_of_le (Nat.le_of_not_gt hn),
      List.headD_nil]

theorem scheduledSmallCell_mem_initial (top : ℕ) (cs : List ℕ) (j : ℕ)
    (i : Fin (scheduledSmallLength (cs.drop j))) :
    scheduledSmallCell top (cs.drop j) i ∈ initialSmallCellList top cs := by
  apply scheduledSmallCell_property
  · exact mem_initialSmallCellList_of_eq_or_mem top cs top (Or.inl rfl)
  · intro c hc
    exact mem_initialSmallCellList_of_eq_or_mem top cs c
      (Or.inr (List.mem_of_mem_drop hc))

theorem selected_cell_prime_range
    {A B : Set ℕ} {N hi j : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D target j)
    (hindex : Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (p : ℕ) (hp : p ∈ selectedTailCellPrimes A B N X hi D j) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ) := by
  refine ⟨h.subset_initialRegularPrimeRange hp, ?_⟩
  exact (Real.exp_le_exp.mpr hindex).trans (h.2.2.2.2.2.2 p hp).2.1.le

theorem completedCompensationSets_range
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (n p : ℕ) (hp : p ∈ completedCompensationSets A B N X hi D top cs n) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((1 / 100 : ℝ) * L)) ≤ (p : ℝ) := by
  obtain ⟨t, ht⟩ := completedCompensationCell_selected htop hcs n
  exact selected_cell_prime_range ht
    (hlower _ (completedCompensationCell_mem_initial top cs n)) p hp

theorem scheduledRegularPrimeSets_range
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (hL : 0 ≤ L)
    (hlower : ∀ j ∈ initialSmallCellList top cs, Real.exp ((1 / 100 : ℝ) * L) ≤ (j : ℝ))
    (hbulk : Qb ⊆ initialRegularPrimeRange L)
    (hbulklower : ∀ p ∈ Qb, Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ))
    (n m j : ℕ) (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m)
    (p : ℕ) (hp : p ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N X hi D) Qb top (cs.drop j) n m i) :
    p ∈ initialRegularPrimeRange L ∧
      Real.exp (Real.exp ((39 / 10000 : ℝ) * L)) ≤ (p : ℝ) := by
  rcases i with ⟨u, i | i⟩
  · have hm := scheduledSmallCell_mem_initial top cs j i
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcs _ hm
    obtain ⟨hmem, hlow⟩ := selected_cell_prime_range ht (hlower _ hm) p hp
    refine ⟨hmem, (le_trans ?_ hlow)⟩
    apply Real.exp_le_exp.mpr
    apply Real.exp_le_exp.mpr
    nlinarith only [hL]
  · exact ⟨hbulk hp, hbulklower p hp⟩

theorem scheduledSmallLower_prime_bound (A B : Set ℕ) (N hi top : ℕ)
    (X : ℝ) (D Qb : Finset ℕ) (cs : List ℕ) (n m : ℕ)
    (i : TreeLeafIndex n × Fin (scheduledSmallLength cs)) (p : ℕ)
    (hp : p ∈ scheduledRegularPrimeSets
      (selectedTailCellPrimes A B N X hi D) Qb top cs n m (i.1, .inl i.2)) :
    Real.exp (scheduledSmallLower top cs n i) ≤ (p : ℝ) := by
  have hmem := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).1
  obtain ⟨hprime, _, hlo, _⟩ := mem_primeLogCellSet_iff.mp hmem
  apply (Real.le_log_iff_exp_le (by exact_mod_cast hprime.pos)).mp
  dsimp only [scheduledSmallLower]
  linarith

theorem scheduledRegularPrimeSets_sub_mass
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (P : Finset ℕ) (hP : initialRegularPrimeRange L ⊆ P) (hbulk : Qb ⊆ P)
    (hmass : Real.exp (-(2 * L)) ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹)
    (n m j : ℕ) (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m) :
    let Q := scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
      Qb top (cs.drop j) n m i
    Q ⊆ P ∧ Real.exp (-(2 * L)) ≤ ∑ p ∈ Q, (p : ℝ)⁻¹ := by
  intro Q
  rcases i with ⟨u, i | i⟩
  · have hm := scheduledSmallCell_mem_initial top cs j i
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcs _ hm
    exact ⟨ht.subset_initialRegularPrimeRange.trans hP, ht.2.2.2.1⟩
  · exact ⟨hbulk, hmass⟩

theorem scheduledRegularPrior_normalized
    {A B : Set ℕ} {N hi top : ℕ} {a C L X target : ℝ} {D Qb : Finset ℕ}
    {cs : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L X hi D target top)
    (hcs : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) cs targets)
    (P : Finset ℕ) (hP : initialRegularPrimeRange L ⊆ P) (hbulk : Qb ⊆ P)
    (hmass : Real.exp (-(2 * L)) ≤ ∑ p ∈ Qb, (p : ℝ)⁻¹)
    (n m j : ℕ) (i : MovingRegularSlot n (scheduledSmallLength (cs.drop j)) m) :
    let ν := scheduledRegularPrior
      (fun c => primeSubsetPrior P (selectedTailCellPrimes A B N X hi D c))
      (primeSubsetPrior P Qb) top (cs.drop j) n m
    (∑ p : P, ν i p) = 1 ∧
      (∀ p : P, 0 ≤ ν i p ∧ (p : ℝ) * ν i p ≤ Real.exp (2 * L)) := by
  intro ν
  have hd := scheduledRegularPrimeSets_sub_mass htop hcs P hP hbulk hmass n m j i
  let Q := scheduledRegularPrimeSets (selectedTailCellPrimes A B N X hi D)
    Qb top (cs.drop j) n m i
  have he : ν i = primeSubsetPrior P Q :=
    congrFun (scheduledRegularPrior_prime (selectedTailCellPrimes A B N X hi D)
      Qb P top (cs.drop j) n m) i
  rw [he]
  refine ⟨primeSubsetPrior_mass P Q hd.1 ((Real.exp_pos _).trans_le hd.2).ne', ?_⟩
  intro p
  refine ⟨primeSubsetPrior_nonneg P Q p, (prime_mul_primeSubsetPrior_le P Q p).trans ?_⟩
  have h := inv_anti₀ (Real.exp_pos _) hd.2
  simpa only [Real.exp_neg, inv_inv] using h

end Ostmann

end OAI
