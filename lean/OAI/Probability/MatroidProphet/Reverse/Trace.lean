import OAI.Probability.MatroidProphet.Reverse.Hazard
import OAI.Probability.MatroidProphet.Density.Birth

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

structure ReverseTransition (α : Type*) where
  time : ℤ
  before : ℕ → Set α
  after : ℕ → Set α

noncomputable def reverseTrace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → List (ReverseTransition α)
  | 0, _, _, _ => []
  | m+1, k, S, C =>
      ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ ::
      reverseTrace M hE κ D G n m (k-1) ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseCost_le_of_trace (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (f g : ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hfg : ∀ t ∈ reverseTrace M hE κ D G n m k S C,
      f t.time t.before t.after ≤ g t.time t.before t.after) :
    reverseCost M hE κ D G n f m k S C ≤ reverseCost M hE κ D G n g m k S C := by
  induction m generalizing k S with
  | zero => exact le_rfl
  | succ m ih =>
    rw [reverseCost, reverseCost]
    apply add_le_add (hfg ⟨k, S, (reverseStepTree M hE κ k D S G n).run C⟩ (by simp [reverseTrace]))
    exact ih _ _ (fun t ht => hfg t (by simp only [reverseTrace, List.mem_cons]; exact Or.inr ht))

noncomputable def traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) : Finset ℝ :=
  univ.biUnion (fun C : Finset α => ((reverseTrace M hE κ D G n m k S C).map
    (fun t => reverseHazard M hE κ D G q d h t.time t.before)).toFinset)

lemma mem_traceHazards (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (q : α → ℝ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α) (t : ReverseTransition α)
    (ht : t ∈ reverseTrace M hE κ D G n m k S C) :
    reverseHazard M hE κ D G q d h t.time t.before ∈ traceHazards M hE κ D G n q d h m k S := by
  exact mem_biUnion.mpr ⟨C, mem_univ C, List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩)⟩

noncomputable def reverseFinal (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) :
    ℕ → ℤ → (ℕ → Set α) → Finset α → (ℕ → Set α)
  | 0, _, S, _ => S
  | m+1, k, S, C => reverseFinal M hE κ D G n m (k-1)
      ((reverseStepTree M hE κ k D S G n).run C) C

lemma reverseStepTree_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    (reverseStepTree M hE κ k D S G n).run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j k := by
  rw [reverseStepTree_run_coordinate M hE κ k D S G n hG C hj]
  calc
    _ = reverseNominal M hE κ D (fun i => (C : Set α) ∩ (G i : Set α))
        (fun i => nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k+1)) k j := by
      apply reverseNominal_congr_before
      · intro i hi; rfl
      · intro i hi; exact hS i (by omega)
    _ = _ := reverseNominal_agrees M hE κ D _ k j

lemma reverseFinal_path (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (C : Finset α)
    (hS : ∀ j ≤ n, S j = nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1))
    {j : ℕ} (hj : j ≤ n) :
    reverseFinal M hE κ D G n m k S C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (k+1-m) := by
  induction m generalizing k S with
  | zero => simpa only [reverseFinal, Nat.cast_zero, sub_zero] using hS j hj
  | succ m ih =>
    rw [reverseFinal]
    have hs' : ∀ i ≤ n, (reverseStepTree M hE κ k D S G n).run C i =
        nominalPath M hE κ D (fun l => (C : Set α) ∩ (G l : Set α)) i (k-1+1) := by
      intro i hi
      simpa only [sub_add_cancel] using reverseStepTree_path M hE κ D G n hG k S C hS hi
    rw [ih (k-1) _ hs']
    congr 1
    omega

lemma reverseFinal_from_univ (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j)))
    (h : ℕ) (hh : h ≤ n) (C : Finset α) :
    reverseFinal M hE κ D G n (pathHorizon h + 1) (-1) (fun _ => Set.univ) C h = M.closure ∅ := by
  rw [reverseFinal_path M hE κ D G n hG (pathHorizon h+1) (-1) (fun _ => Set.univ) C
    (fun j hj => by simpa only [neg_add_cancel] using
      (nominalPath_nonnegative M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (by omega : (0:ℤ) ≤ -1+1)).symm) hh]
  apply nominalPath_early
  unfold pathHorizon activation
  omega

noncomputable def exitCost (d : α) (h : ℕ) (_ : ℤ) (S S' : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ d ∉ S' h then 1 else 0

lemma reverseCost_exit_telescope (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ) (d : α) (h : ℕ)
    (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) (C : Finset α) :
    reverseCost M hE κ D G n (exitCost d h) m k S C =
      (if d ∈ S h then 1 else 0) - (if d ∈ reverseFinal M hE κ D G n m k S C h then 1 else 0) := by
  induction m generalizing k S with
  | zero => by_cases hs : d ∈ S h <;> simp [reverseCost, reverseFinal, hs]
  | succ m ih =>
    rw [reverseCost, reverseFinal, ih (k-1) _ (reverseStepTree_closed M hE κ k D S G n C)]
    have hc := reverseStepTree_contracts M hE κ k D S G n closed C h
    by_cases hs : d ∈ S h <;> by_cases hn : d ∈ (reverseStepTree M hE κ k D S G n).run C h
    · simp [exitCost, hs, hn]
    · simp [exitCost, hs, hn]; ring
    · exact (hs (hc hn)).elim
    · simp [exitCost, hs, hn]

lemma reverse_exit_total_one (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    reverseMeanCost M hE κ D G n q (exitCost d h) (pathHorizon h+1) (-1) (fun _ => Set.univ) = 1 := by
  unfold reverseMeanCost
  have hp : ∀ C : Finset α, reverseCost M hE κ D G n (exitCost d h)
      (pathHorizon h+1) (-1) (fun _ => Set.univ) C = 1 := by
    intro C
    rw [reverseCost_exit_telescope M hE κ D G n d h (pathHorizon h+1) (-1) _
      (reverseClosed_univ M hE κ D (-1)) C, reverseFinal_from_univ M hE κ D G n hG h hh C]
    simp [hd]
  exact (bitsExpectation_congr q univ (fun C _ => hp C)).trans (bitsExpectation_const q univ 1)

end MatroidProphet

end OAI
