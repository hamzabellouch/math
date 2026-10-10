import OAI.Probability.SwitchChain.PairCrossToggleTransport
import OAI.Probability.SwitchChain.SliceNormalizedFamily

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.PairFiber

attribute [local instance] Classical.propDecidable

def cardSliceEquivPowerset {V : Type*} [Fintype V] (q : ℕ) :
    SlicePermutationAction.Slice V q ≃ SliceNormalized.State V q where
  toFun S := ⟨S.val, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, S.property⟩⟩
  invFun S := ⟨S.val, (Finset.mem_powersetCard.mp S.property).2⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

def stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateFiber G i j ≃
      SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card :=
  ((stateFiberEquiv G i j hij).trans (assignmentSliceEquiv G.val i j)).trans
    (cardSliceEquivPowerset _)

theorem stateFiberNormalizedEquiv_mem {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (H : StateFiber G i j) (x : singletonSet G.val i j) :
    x ∈ (stateFiberNormalizedEquiv G i j hij H).val ↔
      H.val.val.Adj i x.val := by
  change x ∈ (leftSet H.val.val i j).subtype
    (fun z => z ∈ singletonSet G.val i j) ↔ _
  rw [Finset.mem_subtype, mem_leftSet]
  have hx : x.val ∈ singletonSet H.val.val i j := by
    rw [singletonSet_eq_of_key_eq H.property]
    exact x.property
  obtain ⟨hxo, hxor⟩ := (mem_singletonSet H.val.val i j x.val).mp hx
  rcases hxor with ht | ht <;> simp_all

theorem raw_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceNormalized.raw (leftSet G.val i j).card x y
      (stateFiberNormalizedEquiv G i j hij H) =
      if x = y then 0 else
        (if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) -
          SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
            (leftSet G.val i j).card := by
  simp only [SliceNormalized.raw,
    SliceMoments.centeredEqual, SliceMoments.equalIndicator,
    stateFiberNormalizedEquiv_mem]

theorem equalIndicator_stateFiberNormalizedEquiv {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (H : StateFiber G i j) :
    SliceMoments.equalIndicator x y (stateFiberNormalizedEquiv G i j hij H).val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0 := by
  simp only [SliceMoments.equalIndicator, stateFiberNormalizedEquiv_mem]

theorem stateFiber_average_equality {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y) :
    (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) /
        (Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card : ℝ) =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  let e := stateFiberNormalizedEquiv G i j hij
  have hs : (∑ H : StateFiber G i j,
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) =
      ∑ S : SliceNormalized.State (singletonSet G.val i j) (leftSet G.val i j).card,
        SliceMoments.equalIndicator x y S.val := by
    apply Fintype.sum_equiv e
    intro H
    exact (equalIndicator_stateFiberNormalizedEquiv G i j hij x y H).symm
  rw [hs]
  have hq : (leftSet G.val i j).card ≤
      (Finset.univ : Finset (singletonSet G.val i j)).card := by
    simpa using Finset.card_le_card (leftSet_subset_singletonSet G.val i j)
  have hm := SliceMoments.average_equalIndicator
    (Finset.univ : Finset (singletonSet G.val i j)) (leftSet G.val i j).card hq
    x y (Finset.mem_univ x) (Finset.mem_univ y) hxy
  simpa only [SliceMoments.average, Finset.sum_coe_sort, Finset.card_univ,
    Fintype.card_coe] using hm

theorem stateFiber_sum_eq_fiberStates {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (f : GraphState n d → ℝ) :
    (∑ H : StateFiber G i j, f H.val) =
      ∑ H ∈ PairResampling.fiberStates {i, j} G, f H := by
  let e : StateFiber G i j ≃ PairResampling.fiberStates {i, j} G :=
    { toFun H := ⟨H.val, (PairResampling.mem_fiberStates {i, j} G H.val).mpr
        ((sameFiber_iff_key_eq i j hij G.val H.val.val).mpr H.property.symm)⟩
      invFun H := ⟨H.val, ((sameFiber_iff_key_eq i j hij G.val H.val.val).mp
        ((PairResampling.mem_fiberStates {i, j} G H.val).mp H.property)).symm⟩
      left_inv H := by apply Subtype.ext; rfl
      right_inv H := by apply Subtype.ext; rfl }
  calc
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f (e.symm H).val :=
      (Equiv.sum_comp e.symm (fun H : StateFiber G i j => f H.val)).symm
    _ = ∑ H : PairResampling.fiberStates {i, j} G, f H.val := rfl
    _ = _ := Finset.sum_coe_sort _ _

theorem expectation_eq_equalMean_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0) :
    PairResampling.expectation n d {i, j} f G =
      SliceMoments.equalMean (Finset.univ : Finset (singletonSet G.val i j))
        (leftSet G.val i j).card := by
  rw [PairResampling.expectation_eq_average, fiberStates_card G i j hij,
    ← stateFiber_sum_eq_fiberStates G i j hij]
  simp_rw [hf]
  exact stateFiber_average_equality G i j hij x y hxy

theorem fluctuation_eq_raw_of_fiber {n : ℕ} {d : Fin n → ℕ}
    (G : GraphState n d) (i j : Fin n) (hij : i ≠ j)
    (x y : singletonSet G.val i j) (hxy : x ≠ y)
    (f : PairResampling.StateSpace n d)
    (hf : ∀ H : StateFiber G i j, f H.val =
      if H.val.val.Adj i x.val ↔ H.val.val.Adj i y.val then (1 : ℝ) else 0)
    (H : StateFiber G i j) :
    PairResampling.fluctuation n d {i, j} f H.val =
      SliceNormalized.raw (leftSet G.val i j).card x y
        (stateFiberNormalizedEquiv G i j hij H) := by
  have hexp : PairResampling.expectation n d {i, j} f H.val =
      PairResampling.expectation n d {i, j} f G :=
    PairResampling.expectation_mem {i, j} f H.val G
      ((sameFiber_iff_key_eq i j hij H.val.val G.val).mpr H.property)
  rw [PairResampling.fluctuation_eq_sub]
  change f H.val - PairResampling.expectation n d {i, j} f H.val = _
  rw [hexp, expectation_eq_equalMean_of_fiber G i j hij x y hxy f hf,
    hf H, raw_stateFiberNormalizedEquiv]
  simp only [hxy, ite_false]

end Problem315.PairFiber

end

end OAI
