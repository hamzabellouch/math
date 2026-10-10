import OAI.Probability.SwitchChain.PairFiberOrientation
import OAI.Probability.SwitchChain.PairEqualityProjection

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

@[simp] theorem observable_swap_right (i k l : Fin n) :
    observable (d := d) i l k = observable i k l := by
  ext G
  change (if G.val.Adj i l ↔ G.val.Adj i k then (1 : ℝ) else 0) =
    if G.val.Adj i k ↔ G.val.Adj i l then 1 else 0
  simp only [iff_comm]

@[simp] theorem centered_swap_right (i j k l : Fin n) :
    centered (d := d) i j l k = centered i j k l := by
  simp only [centered, observable_swap_right]

@[simp] theorem active_swap_left (i j k l : Fin n) (G : GraphState n d) :
    active j i k l G ↔ active i j k l G := by
  simp only [active, singletonSet_swap]

@[simp] theorem active_swap_right (i j k l : Fin n) (G : GraphState n d) :
    active i j l k G ↔ active i j k l G := by
  exact and_comm

theorem observable_eq_of_active (i j k l : Fin n) (G : GraphState n d)
    (ha : active i j k l G) : observable i k l G = observable j k l G := by
  change (if G.val.Adj i k ↔ G.val.Adj i l then (1 : ℝ) else 0) =
    if G.val.Adj j k ↔ G.val.Adj j l then 1 else 0
  simp only [singleton_adj_equal_swap G.val i j k l ha.1 ha.2]

theorem centered_eq_of_active (i j k l : Fin n) (hij : i ≠ j)
    (G : GraphState n d) (ha : active i j k l G) :
    centered i j k l G = centered j i k l G := by
  unfold centered
  rw [fluctuation_eq_sub, fluctuation_eq_sub]
  change observable i k l G - expectation n d {i,j} (observable i k l) G =
    observable j k l G - expectation n d {j,i} (observable j k l) G
  rw [observable_eq_of_active i j k l G ha, Finset.pair_comm j i]
  congr 1
  rw [expectation_eq_average, expectation_eq_average]
  congr 1
  apply Finset.sum_congr rfl
  intro H hH
  exact observable_eq_of_active i j k l H
    ((active_sameFiber i j k l hij ((mem_fiberStates {i,j} G H).mp hH)).mp ha)

theorem gated_centered_swap_left (i j k l : Fin n) (hij : i ≠ j)
    (G H : GraphState n d) (h : SameFiber {i,j} G.val H.val) :
    (if active i j k l G then centered i j k l H else 0) =
      (if active j i k l G then centered j i k l H else 0) := by
  simp only [active_swap_left]
  by_cases ha : active i j k l G
  · simp only [ite_eq_left ha]
    exact centered_eq_of_active i j k l hij H ((active_sameFiber i j k l hij h).mp ha)
  · simp only [ite_eq_right ha]

theorem equalitySpace_le_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l ≤ equalitySpace j i k l := by
  intro f hf G
  obtain ⟨c,hc⟩ := hf G
  refine ⟨c, fun H h => ?_⟩
  have h' : SameFiber {i,j} G.val H.val := by
    simpa only [Finset.pair_comm j i] using h
  rw [hc H h', gated_centered_swap_left i j k l hij G H h']

theorem equalitySpace_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    equalitySpace (d := d) i j k l = equalitySpace j i k l :=
  le_antisymm (equalitySpace_le_swap_left i j k l hij)
    (equalitySpace_le_swap_left j i k l hij.symm)

theorem equalitySpace_swap_right (i j k l : Fin n) :
    equalitySpace (d := d) i j k l = equalitySpace i j l k := by
  ext f
  simp only [equalitySpace, Submodule.mem_mk,
    active_swap_right, centered_swap_right]

theorem projection_swap_left (i j k l : Fin n) (hij : i ≠ j) :
    projection (d := d) i j k l = projection j i k l := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_left i j k l hij)

theorem projection_swap_right (i j k l : Fin n) :
    projection (d := d) i j k l = projection i j l k := by
  exact congrArg (fun M : Submodule ℝ (StateSpace n d) => M.starProjection)
    (equalitySpace_swap_right i j k l)

theorem projection_eq_of_left_pair_eq (i j i' j' k l : Fin n) (hij : i ≠ j)
    (h : ({i,j} : Finset (Fin n)) = {i',j'}) :
    projection (d := d) i j k l = projection i' j' k l := by
  have hs : ({i,j} : Set (Fin n)) = {i',j'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_left _ _ _ _ hij

theorem projection_eq_of_right_pair_eq (i j k l k' l' : Fin n)
    (h : ({k,l} : Finset (Fin n)) = {k',l'}) :
    projection (d := d) i j k l = projection i j k' l' := by
  have hs : ({k,l} : Set (Fin n)) = {k',l'} := by
    simpa only [Finset.coe_pair] using congrArg (fun a : Finset (Fin n) => (a : Set (Fin n))) h
  rcases Set.pair_eq_pair_iff.mp hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact projection_swap_right _ _ _ _

end Problem315.PairEquality

end

end OAI
