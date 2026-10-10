import OAI.Probability.MatroidProphet.Reverse.BirthSafety

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

lemma reverseCost_add_steps (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m r : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost (m+r) k S C =
      reverseCost M hE κ D G n cost m k S C +
        reverseCost M hE κ D G n cost r (k-m) (reverseFinal M hE κ D G n m k S C) C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, reverseFinal, Nat.cast_zero, sub_zero, zero_add]
  | succ m ih =>
    rw [Nat.succ_add, reverseCost, reverseCost, reverseFinal, ih]
    have ht : k - 1 - (m:ℤ) = k - ((m+1:ℕ):ℤ) := by omega
    rw [ht]
    ring

lemma reverseCost_eq_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n cost m k S C =
      ∑ i ∈ range m, cost (k-i) (reverseFinal M hE κ D G n i k S C)
        ((reverseStepTree M hE κ (k-i) D (reverseFinal M hE κ D G n i k S C) G n).run C) := by
  induction m with
  | zero => simp only [reverseCost, range_zero, sum_empty]
  | succ m ih =>
    rw [reverseCost_add_steps M hE κ D G n cost m 1, ih, sum_range_succ]
    simp only [reverseCost, add_zero]

noncomputable def pathExitSquare (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ) (m : ℕ)
    (C : Finset α) : ℝ :=
  if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
    (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
      (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0

lemma reverse_square_eq_path_sum (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) :
    reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) m (-1) (fun _ => Set.univ) =
      ∑ i ∈ range m, bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  unfold reverseMeanCost
  rw [← bitsExpectation_sum]
  apply bitsExpectation_congr
  intro C hC
  rw [reverseCost_eq_sum]
  apply sum_congr rfl
  intro i hi
  have hS : ∀ j ≤ n, (fun _ => Set.univ) j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-1+1) := by
    intro j hj
    exact (nominalPath_nonnegative M hE κ D _ j (by omega)).symm
  have hf (j : ℕ) (hj : j ≤ n) : reverseFinal M hE κ D G n i (-1) (fun _ => Set.univ) C j =
      nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) j (-(i:ℤ)) := by
    simpa only [neg_add_cancel, zero_sub] using reverseFinal_path M hE κ D G n hG i (-1) _ C hS hj
  have ht : (-1:ℤ) - i = -(i:ℤ)-1 := by omega
  simp only [squareHazardCost, pathExitSquare, ht, hf h hh]
  rw [reverseHazard_state_congr M hE κ D _ _ G q _ h d (fun j hj => hf j (by omega))]

theorem path_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) :
    (((2:ℝ)^12)⁻¹) / 2 ≤
      ∑ i ∈ range (pathHorizon h+1), bitsExpectation q univ (pathExitSquare M hE κ D G q d h i) := by
  rw [← reverse_square_eq_path_sum M hE κ D G h hG q d h le_rfl]
  exact reverse_squared_exit_mass M hE κ D G h hG q hq0 hq1 d hd h le_rfl

end MatroidProphet

end OAI
