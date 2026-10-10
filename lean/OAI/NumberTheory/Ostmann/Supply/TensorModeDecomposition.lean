import OAI.NumberTheory.Ostmann.Supply.TensorModes

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped TensorProduct BigOperators

@[simp] theorem exactMode_succ (E : ℕ → FiniteHilbertSpace) (n : ℕ) (s : Finset ℕ) :
    exactMode E (n+1) s = TensorProduct.mapL (exactMode E n s)
      (if n ∈ s then centeredPart (E n) else scalarPart (E n)) := rfl

@[simp] theorem exactMode_insert_top (E : ℕ → FiniteHilbertSpace) (n : ℕ) (s : Finset ℕ) :
    exactMode E n (insert n s) = exactMode E n s := by
  apply tensorOp_congr
  intro i hi
  simp [show i ≠ n by omega]

@[simp] theorem exactMode_erase_top (E : ℕ → FiniteHilbertSpace) (n : ℕ) (s : Finset ℕ) :
    exactMode E n (s.erase n) = exactMode E n s := by
  apply tensorOp_congr
  intro i hi
  simp [show i ≠ n by omega]

theorem sum_all_exactModes (E : ℕ → FiniteHilbertSpace) (n : ℕ) :
    (∑ s ∈ (range n).powerset, exactMode E n s) = 1 := by
  induction n with
  | zero =>
    change (∑ s ∈ ({∅} : Finset (Finset ℕ)), (1 : ℂ →L[ℂ] ℂ)) = 1
    rw [sum_singleton]
  | succ n ih =>
    rw [range_add_one, sum_powerset_insert (by simp : n ∉ range n)]
    have hfirst : (∑ s ∈ (range n).powerset, exactMode E (n+1) s) =
        TensorProduct.mapL (∑ s ∈ (range n).powerset, exactMode E n s) (scalarPart (E n)) := by
      rw [mapL_sum_left]
      apply sum_congr rfl
      intro s hs
      have hns : n ∉ s := fun hn => (by have := mem_range.mp (mem_powerset.mp hs hn); omega)
      simp only [exactMode_succ, ite_eq_right hns]
      rfl
    have hsecond : (∑ s ∈ (range n).powerset, exactMode E (n+1) (insert n s)) =
        TensorProduct.mapL (∑ s ∈ (range n).powerset, exactMode E n s) (centeredPart (E n)) := by
      rw [mapL_sum_left]
      apply sum_congr rfl
      intro s hs
      simp only [exactMode_succ, exactMode_insert_top, mem_insert_self, ite_true]
      rfl
    rw [hfirst, hsecond]
    change TensorProduct.mapL (∑ s ∈ (range n).powerset, exactMode E n s) (scalarPart (E n)) +
      TensorProduct.mapL (∑ s ∈ (range n).powerset, exactMode E n s) (centeredPart (E n)) =
      (ContinuousLinearMap.id ℂ
        (tensorSpace (fun i => augmentedSpace (E i)) n ⊗[ℂ] augmentedSpace (E n)))
    rw [← TensorProduct.mapL_add_right, ih, scalar_add_centered]
    exact TensorProduct.mapL_id_id

theorem lowModes_comp_of_high_zero {E F : ℕ → FiniteHilbertSpace} (n K : ℕ)
    (T : tensorSpace (fun i => augmentedSpace (E i)) n →L[ℂ]
      tensorSpace (fun i => augmentedSpace (F i)) n)
    (hhigh : ∀ s ⊆ range n, K < s.card → (exactMode F n s).comp T = 0) :
    (lowModes F n K).comp T = T := by
  ext x
  change lowModes F n K (T x) = T x
  have hfull : (∑ s ∈ (range n).powerset, exactMode F n s (T x)) = T x := by
    rw [← _root_.sum_apply, sum_all_exactModes]
    rfl
  calc
    _ = ∑ s ∈ retainedModes n K, exactMode F n s (T x) := by simp [lowModes]
    _ = ∑ s ∈ (range n).powerset, exactMode F n s (T x) := by
      apply sum_subset (filter_subset _ _)
      intro s hs hnot
      have hcard : K < s.card := by
        by_contra h
        exact hnot (mem_filter.mpr ⟨hs, by omega⟩)
      exact congrArg (fun f => f x) (hhigh s (mem_powerset.mp hs) hcard)
    _ = _ := hfull

theorem comp_lowModes_of_high_zero {E F : ℕ → FiniteHilbertSpace} (n K : ℕ)
    (T : tensorSpace (fun i => augmentedSpace (E i)) n →L[ℂ]
      tensorSpace (fun i => augmentedSpace (F i)) n)
    (hhigh : ∀ s ⊆ range n, K < s.card → T.comp (exactMode E n s) = 0) :
    T.comp (lowModes E n K) = T := by
  ext x
  change T (lowModes E n K x) = T x
  have hfull : (∑ s ∈ (range n).powerset, T (exactMode E n s x)) = T x := by
    rw [← map_sum, ← _root_.sum_apply, sum_all_exactModes]
    rfl
  calc
    _ = ∑ s ∈ retainedModes n K, T (exactMode E n s x) := by simp [lowModes, map_sum]
    _ = ∑ s ∈ (range n).powerset, T (exactMode E n s x) := by
      apply sum_subset (filter_subset _ _)
      intro s hs hnot
      have hcard : K < s.card := by
        by_contra h
        exact hnot (mem_filter.mpr ⟨hs, by omega⟩)
      exact congrArg (fun f => f x) (hhigh s (mem_powerset.mp hs) hcard)
    _ = _ := hfull

end Ostmann.Supply.TensorModes

end

end OAI
