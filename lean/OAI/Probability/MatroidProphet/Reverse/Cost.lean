import OAI.Probability.MatroidProphet.Reverse.Certificates
import OAI.Probability.MatroidProphet.RevealContinuation
import OAI.Probability.MatroidProphet.ProductRestriction

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def reverseCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → ℝ
  | 0, _, _, _ => 0
  | m+1, k, S, C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
      reverseCost M hE κ D G n cost m (k-1)
        ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseCost_congr (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S)
    (C C' : Finset α)
    (agree : ∀ j < n, ∀ e ∈ G j, e ∈ S j → (e ∈ C ↔ e ∈ C')) :
    reverseCost M hE κ D G n cost m k S C = reverseCost M hE κ D G n cost m k S C' := by
  induction m generalizing k S with
  | zero => rfl
  | succ m ih =>
    let V := (range n).biUnion (fun j => (G j).filter (fun e => e ∈ S j))
    have hV : ∀ j < n, (G j).filter (fun e => e ∈ S j) ⊆ V := by
      intro j hj e he
      exact mem_biUnion.mpr ⟨j, mem_range.mpr hj, he⟩
    have ha : ∀ e ∈ V, (e ∈ C ↔ e ∈ C') := by
      intro e he
      obtain ⟨j, hj, hje⟩ := mem_biUnion.mp he
      exact agree j (mem_range.mp hj) e (mem_filter.mp hje).1 (mem_filter.mp hje).2
    have hs := (reverseStepTree M hE κ k D S G n).run_congr V C C'
      (reverseStepTree_fresh M hE κ k D S G n hG V hV) ha
    simp only [reverseCost, hs]
    congr 1
    apply ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C')
    intro j hj e heG heS
    exact agree j hj e heG (reverseStepTree_contracts M hE κ k D S G n closed C' j heS)

lemma reverseCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => f k S S' + g k S S') m k S C =
      reverseCost M hE κ D G n f m k S C + reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => a * f k S S') m k S C =
      a * reverseCost M hE κ D G n f m k S C := by
  induction m generalizing k S with
  | zero => simp [reverseCost]
  | succ m ih => simp only [reverseCost, ih]; ring

lemma reverseCost_mono (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S S', f k S S' ≤ g k S S')
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih => exact add_le_add (hfg _ _ _) (ih _ _)

noncomputable def reverseMeanCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : ℝ :=
  bitsExpectation q univ (reverseCost M hE κ D G n cost m k S)

lemma reverseCost_erase_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C =
      reverseCost M hE κ D G n cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)
        (C \ (reverseStepTree M hE κ k D S G n).queried C) := by
  apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
    (reverseStepTree_closed M hE κ k D S G n C)
  intro j hj e heG heS
  have he := reverseStepTree_remaining M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩)
  simp only [mem_sdiff, (mem_sdiff.mp he).2, not_false_eq_true, and_true]

theorem reverseMeanCost_succ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q cost (m+1) k S =
      bitsExpectation q univ (fun C => cost k S ((reverseStepTree M hE κ k D S G n).run C) +
        reverseMeanCost M hE κ D G n q cost m (k-1) ((reverseStepTree M hE κ k D S G n).run C)) := by
  let tree := reverseStepTree M hE κ k D S G n
  let f := fun (S' : ℕ → Set α) (C : Finset α) => reverseCost M hE κ D G n cost m (k-1) S' C
  have hfresh : tree.Fresh univ := reverseStepTree_fresh M hE κ k D S G n hG univ
    (fun _ _ => subset_univ _)
  have herase : bitsExpectation q univ (fun C => f (tree.run C) C) =
      bitsExpectation q univ (fun C => f (tree.run C) (C \ tree.queried C)) := by
    apply bitsExpectation_congr
    intro C hC
    exact reverseCost_erase_step M hE κ D G n hG cost m k S closed C
  have hrestrict : bitsExpectation q univ (fun C => bitsExpectation q (univ \ tree.queried C)
      (f (tree.run C))) = bitsExpectation q univ (fun C => bitsExpectation q univ (f (tree.run C))) := by
    apply bitsExpectation_congr
    intro C hC
    symm
    apply bitsExpectation_restrict q univ _ (subset_univ _) (f (tree.run C))
    intro T T' hT
    apply reverseCost_congr M hE κ D G n hG cost m (k-1) _
      (reverseStepTree_closed M hE κ k D S G n C)
    intro j hj e heG heS
    exact hT e (reverseStepTree_remaining M hE κ k D S G n hG univ
      (fun _ _ => subset_univ _) closed C j hj (mem_filter.mpr ⟨heG, heS⟩))
  have htower := tree.continuation_expectation q univ hfresh f
  change bitsExpectation q univ (fun C => cost k S (tree.run C) + f (tree.run C) C) =
    bitsExpectation q univ (fun C => cost k S (tree.run C) + bitsExpectation q univ (f (tree.run C)))
  rw [bitsExpectation_add, bitsExpectation_add, herase, htower, hrestrict]

@[simp] lemma reverseMeanCost_zero (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (cost : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q cost 0 k S = 0 := by
  simp only [reverseMeanCost, reverseCost, bitsExpectation_const]

lemma reverseMeanCost_add (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => f k S S' + g k S S') m k S =
      reverseMeanCost M hE κ D G n q f m k S + reverseMeanCost M hE κ D G n q g m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_add]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_add M hE κ D G n f g m k S C)

lemma reverseMeanCost_mul (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (f : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ) (a : ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => a * f k S S') m k S =
      a * reverseMeanCost M hE κ D G n q f m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_mul_left]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_mul M hE κ D G n f a m k S C)

theorem reverseMeanCost_le_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) ≤
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S ≤ reverseMeanCost M hE κ D G n q g m k S := by
  induction m generalizing k S with
  | zero => simp only [reverseMeanCost_zero, le_refl]
  | succ m ih =>
    rw [reverseMeanCost_succ M hE κ D G n hG q f m k S closed,
      reverseMeanCost_succ M hE κ D G n hG q g m k S closed,
      bitsExpectation_add, bitsExpectation_add]
    apply add_le_add (hfg k S closed)
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)

theorem reverseMeanCost_eq_of_step (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (hfg : ∀ k S, ReverseClosed M hE κ D k S →
      bitsExpectation q univ (fun C => f k S ((reverseStepTree M hE κ k D S G n).run C)) =
      bitsExpectation q univ (fun C => g k S ((reverseStepTree M hE κ k D S G n).run C)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q f m k S = reverseMeanCost M hE κ D G n q g m k S :=
  le_antisymm (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 f g
    (fun k S hS => (hfg k S hS).le) m k S closed)
    (reverseMeanCost_le_of_step M hE κ D G n hG q hq0 hq1 g f
    (fun k S hS => (hfg k S hS).ge) m k S closed)

lemma reverseCost_sum {ι : Type*} (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (I : Finset ι) (f : ι → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) :
    reverseCost M hE κ D G n (fun k S S' => ∑ i ∈ I, f i k S S') m k S C =
      ∑ i ∈ I, reverseCost M hE κ D G n (f i) m k S C := by
  induction m generalizing k S with
  | zero => simp only [reverseCost, sum_const_zero]
  | succ m ih => simp only [reverseCost, ih, sum_add_distrib]

lemma reverseMeanCost_sum {ι : Type*} (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ)
    (I : Finset ι) (f : ι → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) :
    reverseMeanCost M hE κ D G n q (fun k S S' => ∑ i ∈ I, f i k S S') m k S =
      ∑ i ∈ I, reverseMeanCost M hE κ D G n q (f i) m k S := by
  unfold reverseMeanCost
  rw [← bitsExpectation_sum]
  exact bitsExpectation_congr q univ (fun C _ => reverseCost_sum M hE κ D G n I f m k S C)

end MatroidProphet

end OAI
