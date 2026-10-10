import OAI.Probability.SwitchChain.PairFiberEquiv
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber
attribute [local instance] Classical.propDecidable

variable {n : Nat}

theorem pair_neighbor_count (G : SimpleGraph (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (w : Fin n) :
    (({i, j} : Finset (Fin n)).filter (G.Adj w)).card =
      edgeBit G i w + edgeBit G j w := by
  classical
  by_cases hi : G.Adj i w <;> by_cases hj : G.Adj j w <;>
    simp [Finset.filter_insert, Finset.filter_singleton, edgeBit, G.adj_comm w i, G.adj_comm w j, hi, hj, hij]

theorem sameFiber_iff_key_eq (i j : Fin n) (hij : i ≠ j)
    (G H : SimpleGraph (Fin n)) :
    PairResampling.SameFiber {i, j} G H ↔ key i j G = key i j H := by
  classical
  constructor
  · intro h
    apply key_eq_of
    · intro u v hu hv
      exact h.1 u (by simpa [Outside] using hu) v (by simpa [Outside] using hv)
    · exact h.2.1 i (by simp) j (by simp)
    · intro w
      by_cases wi : w = i
      · subst w
        have hi := h.2.1 j (by simp) i (by simp)
        simp [edgeBit, hi]
      by_cases wj : w = j
      · subst w
        have hi := h.2.1 i (by simp) j (by simp)
        simp [edgeBit, hi]
      rw [← pair_neighbor_count G i j hij w, ← pair_neighbor_count H i j hij w]
      exact h.2.2 w (by simp [wi, wj])
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      exact key_outside h (by simpa [Outside] using hu) (by simpa [Outside] using hv)
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · simp
      · exact key_internal h
      · simpa only [G.adj_comm, H.adj_comm] using key_internal h
      · simp
    · intro w hw
      rw [pair_neighbor_count G i j hij w, pair_neighbor_count H i j hij w]
      exact key_count h w

def resamplingFiberEquiv {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G) ≃ Assignment G.val i j := by
  classical
  let e : (PairResampling.fiberStates {i, j} G) ≃ StateFiber G i j :=
    { toFun := fun H => ⟨H.val,
        ((sameFiber_iff_key_eq i j hij G.val H.val.val).mp
          ((PairResampling.mem_fiberStates {i, j} G H.val).mp H.property)).symm⟩
      invFun := fun H => ⟨H.val,
        (PairResampling.mem_fiberStates {i, j} G H.val).mpr
          ((sameFiber_iff_key_eq i j hij G.val H.val.val).mpr H.property.symm)⟩
      left_inv := fun H => by apply Subtype.ext; rfl
      right_inv := fun H => by apply Subtype.ext; rfl }
  exact e.trans (stateFiberEquiv G i j hij)

@[simp] theorem resamplingFiberEquiv_symm_val {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) (T : Assignment G.val i j) :
    ((resamplingFiberEquiv G i j hij).symm T).val =
      ((stateFiberEquiv G i j hij).symm T).val := rfl

theorem fiberStates_card {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    (PairResampling.fiberStates {i, j} G).card =
      Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
  classical
  calc
    _ = Nat.card (PairResampling.fiberStates {i, j} G) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card (Assignment G.val i j) := Nat.card_congr (resamplingFiberEquiv G i j hij)
    _ = _ := assignment_natCard G.val i j

theorem expectation_eq_assignment_average {d : Fin n → Nat}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : PairResampling.StateSpace n d) :
    PairResampling.expectation n d {i, j} f G =
      (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) := by
  classical
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij]
  congr 1
  rw [← Finset.sum_coe_sort]
  exact ((resamplingFiberEquiv G i j hij).symm.sum_comp
    (fun H : (PairResampling.fiberStates {i, j} G) => f H.val)).symm

end Problem315.PairFiber

end

end OAI
