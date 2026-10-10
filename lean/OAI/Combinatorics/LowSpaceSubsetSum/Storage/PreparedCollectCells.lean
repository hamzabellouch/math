import OAI.Combinatorics.LowSpaceSubsetSum.Storage.ComputedFuelCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedBuildCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PreparedParentCells
import OAI.Combinatorics.LowSpaceSubsetSum.Search.PreparedReaderBounds

namespace OAI

/-! # Live storage of the full guarded parent collection

The first prepared context remains live while the second is built. Both
shared right arrays then remain live throughout the stopped join. The
returned safe dictionary replaces the contexts after collection; no list
of emitted matches is retained.
-/

namespace LowSpaceSubsetSum.PreparedCollectCells

variable {n : ℕ}

def contextCells {I : Instance n} {F : IndexedMask n} {P : ℤ}
    {mode : FilteredStream.Mode} (c : PreparedReaderContext.Context I F P mode) : ℕ :=
  ParentLiveState.sharedArrays #[] c.right + ParentLiveState.reader c.state + 16

theorem contextCells_bound (I : Instance n) (F : IndexedMask n) (P : ℤ)
    (mode : FilteredStream.Mode) (c : PreparedReaderContext.Context I F P mode)
    (C : ℕ) (hn : 10000 ≤ n) (hr : c.right.size ≤ C)
    (ht : 2^(c.depth+1) ≤ 4*(C+1)) : contextCells c ≤ inputScale I^2*(C+1) := by
  have ha := ParentLiveBounds.shared_le I C #[] c.right (by simp) hr
  have hs := ParentLiveBounds.reader_le I F P mode c.right c.state C ht
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hcoef : 200*inputScale I ≤ inputScale I^2 := by nlinarith only [hu]
  have hscale := Nat.mul_le_mul_right (C+1) hcoef
  have hbase : inputScale I ≤ inputScale I*(C+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  unfold contextCells
  nlinarith only [ha, hs, hscale, hbase, hu]

/-- The projected return value has no reader or array fields. -/
def resultCells {I : Instance n} {C : ℕ} (out : PreparedParentExecution.Result I C) : ℕ :=
  ParentLiveState.dictionary out.dictionary + 5

theorem resultCells_bound (I : Instance n) (C : ℕ)
    (out : PreparedParentExecution.Result I C) (hn : 10000 ≤ n) :
    resultCells out ≤ inputScale I^2*(C+1) := by
  have hd := ParentLiveState.dictionary_scale I C out.dictionary
  have hu : 10000 ≤ inputScale I := by unfold inputScale; omega
  have hc : 31*inputScale I ≤ inputScale I^2 := by nlinarith only [hu]
  have hm := Nat.mul_le_mul_right (C+1) hc
  have hp : inputScale I ≤ inputScale I*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
  unfold resultCells
  nlinarith only [hd, hu, hm, hp]

def run (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) :
    (Option (PreparedParentExecution.Result D.input D.capacity × ℕ) × ℕ) × ℕ :=
  if BudgetedPreparedParent.setupCharge D.input C ≤ budget then
    let limits := ComputedFuelCells.run D
    let left := PreparedBuildCells.build D F P hF 0
    let right := PreparedBuildCells.build D F P hF 1
    let out := PreparedParentCells.runContexts D.input F D.modulus D.parentResidue D.capacity B
      limits.1.1.first limits.1.1.second limits.1.1.control left.1.1 right.1.1
      (budget-BudgetedPreparedParent.setupCharge D.input C)
    ((out.1.1, limits.1.2+left.1.2+right.1.2+out.1.2+7),
      limits.2+left.2+right.2+out.2+contextCells left.1.1+contextCells right.1.1+32)
  else ((none, 1), 16)

theorem run_value (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B C budget : ℕ) :
    (run D F P hF B C budget).1 = BudgetedPreparedParent.run D F P hF B C budget := by
  by_cases hb : BudgetedPreparedParent.setupCharge D.input C ≤ budget
  · have hv := PreparedParentCells.runContexts_value D.input F D.modulus D.parentResidue D.capacity B
      (ComputedParentFuels.run D).1.first (ComputedParentFuels.run D).1.second
      (ComputedParentFuels.run D).1.control
      (PreparedReaderContext.build D F P hF 0).1 (PreparedReaderContext.build D F P hF 1).1
      (budget-BudgetedPreparedParent.setupCharge D.input C)
    simp only [run, BudgetedPreparedParent.run, ite_eq_left hb, ComputedFuelCells.run_value,
      PreparedBuildCells.build_value]
    rw [congrArg Prod.fst hv, congrArg Prod.snd hv]
  · simp only [run, BudgetedPreparedParent.run, ite_eq_right hb]

private theorem padded_power (R C : ℕ) (h : R ≤ C) :
    2^(Nat.clog 2 R+1) ≤ 4*(C+1) := by
  have hp := Tournament.padded_nodes_le R
    (Tournament.build (fun _ : Unit => (0 : ℤ)) (Nat.clog 2 R) (fun _ => none))
  simp only [Tournament.nodes_exact] at hp
  exact hp.trans (Nat.mul_le_mul_left 4 (by omega))

private theorem scalar_bound (u C fuel left right joined saved₀ saved₁ : ℕ)
    (hu : 10000 ≤ u) (hf : fuel ≤ u^3)
    (hl : left ≤ u^9*(C+1)) (hr : right ≤ u^9*(C+1))
    (hj : joined ≤ u^13*(C+1)) (hs₀ : saved₀ ≤ u^2*(C+1)) (hs₁ : saved₁ ≤ u^2*(C+1)) :
    fuel+left+right+joined+saved₀+saved₁+32 ≤ u^14*(C+1) := by
  have h39 : u^3 ≤ u^9 := pow_le_pow_right' (by omega) (by decide)
  have h29 : u^2 ≤ u^9 := pow_le_pow_right' (by omega) (by decide)
  have h913 : u^9 ≤ u^13 := pow_le_pow_right' (by omega) (by decide)
  have h32 : 32 ≤ u^13*(C+1) := by
    have hpow : u ≤ u^13 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ u) (by decide : 1 ≤ 13)
    have hm : u^13 ≤ u^13*(C+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hf' := hf.trans (h39.trans h913)
  have hf'' := hf'.trans (Nat.le_mul_of_pos_right _ (by omega : 0 < C+1))
  have hl' := hl.trans (Nat.mul_le_mul_right _ h913)
  have hr' := hr.trans (Nat.mul_le_mul_right _ h913)
  have hs₀' := hs₀.trans (Nat.mul_le_mul_right _ (h29.trans h913))
  have hs₁' := hs₁.trans (Nat.mul_le_mul_right _ (h29.trans h913))
  have hcoef : 7*u^13 ≤ u^14 := by
    calc
      _ ≤ u*u^13 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' _ _).symm
  have hfinal := Nat.mul_le_mul_right (C+1) hcoef
  simp only [Nat.mul_assoc] at hfinal
  omega

theorem run_cells (D : RepresentationParentData n) (F : IndexedMask n) (P : StoredRestriction n)
    (hF : F.semantic = D.signs) (B budget : ℕ) (hn : 10000 ≤ n)
    (hl : ∀ j, (D.pair j).left.occurrences.card ≤ D.capacity)
    (hr : ∀ j, (D.pair j).right.occurrences.card ≤ D.capacity)
    (hC : D.capacity ≤ 2^n) (hB : B ≤ D.capacity) :
    (run D F P hF B D.capacity budget).2 ≤ inputScale D.input^14*(D.capacity+1) := by
  let left := (PreparedBuildCells.build D F P hF 0).1.1
  let right := (PreparedBuildCells.build D F P hF 1).1.1
  have hd (j : Fin 2) : (PreparedBuildCells.build D F P hF j).1.1.depth ≤ n := by
    rw [PreparedBuildCells.build_value]
    exact PreparedReaderContext.build_depth D F P hF j ((hl j).trans hC)
  have hp (j : Fin 2) : 2^((PreparedBuildCells.build D F P hF j).1.1.depth+1) ≤
      4*(D.capacity+1) := by
    rw [PreparedBuildCells.build_value]
    change 2^(Nat.clog 2
      (RepresentationStoredArrays.prepare {D with maskRestriction := P.semantic}
        F P.ones P.zeros j).1.1.size+1) ≤ _
    exact padded_power _ _ ((RepresentationStoredArrays.prepare_sizes
      {D with maskRestriction := P.semantic} F P.ones P.zeros j).1.trans (hl j))
  have hrs (j : Fin 2) : (PreparedBuildCells.build D F P hF j).1.1.right.size ≤ D.capacity := by
    rw [PreparedBuildCells.build_value]
    exact (PreparedReaderContext.build_right_size D F P hF j).trans (hr j)
  have hf := ComputedFuelCells.run_cells D hn
  have hlc := PreparedBuildCells.build_cells D F P hF 0 D.capacity hn (hl 0) (hr 0) hC
  have hrc := PreparedBuildCells.build_cells D F P hF 1 D.capacity hn (hl 1) (hr 1) hC
  have hs₀ := contextCells_bound D.input F D.modulus (D.pair 0).mode left D.capacity hn (hrs 0) (hp 0)
  have hs₁ := contextCells_bound D.input F D.modulus (D.pair 1).mode right D.capacity hn (hrs 1) (hp 1)
  rw [run]
  split
  · have hj := PreparedParentCells.runContexts_cells D.input F D.modulus D.parentResidue D.capacity B
      (ComputedFuelCells.run D).1.1.first (ComputedFuelCells.run D).1.1.second
      (ComputedFuelCells.run D).1.1.control left right
      (budget-BudgetedPreparedParent.setupCharge D.input D.capacity) hn
      (hd 0) (hd 1) (hp 0) (hp 1) (hrs 0) (hrs 1) hB
    exact scalar_bound _ _ _ _ _ _ _ _ (by unfold inputScale; omega) hf hlc hrc hj hs₀ hs₁
  · have hu : 10000 ≤ inputScale D.input := by unfold inputScale; omega
    have hp : inputScale D.input ≤ inputScale D.input^14 := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale D.input)
        (by decide : 1 ≤ 14)
    have hm : inputScale D.input^14 ≤ inputScale D.input^14*(D.capacity+1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    simp only
    omega

end LowSpaceSubsetSum.PreparedCollectCells

end OAI
