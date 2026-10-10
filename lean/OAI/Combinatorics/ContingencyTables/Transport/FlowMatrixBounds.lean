import OAI.Combinatorics.ContingencyTables.Machines.FlowMatrixProgram

namespace OAI

/-! # Binary-size bounds for materialized flow updates -/

namespace ContingencyTables.FlowMatrixBounds

open MatchingFPRAS.TreeTyped ResidualGraphProgram FlowEntryProgram FlowMatrixProgram

lemma getD_weight {α : Type} [Codec α] (xs : List α) (d : α)
    (hd : weight d≤ weight xs) (i : ℕ) : weight (xs.getD i d)≤ weight xs := by
  by_cases hi : i< xs.length
  · have he : xs.getD i d=xs[i] := by simp [List.getD_eq_getElem?_getD,hi]
    rw [he]
    exact weight_mem (List.getElem_mem hi)
  · simpa [List.getD_eq_getElem?_getD,hi] using hd

lemma capacityEntry_weight (C : NatMatrix) (u v : ℕ) :
    weight (capacityEntry (C,(u,v)))≤ weight C := by
  have hr : weight (C.getD u [])≤ weight C :=
    getD_weight C [] (by
      rw [weight_nil]
      have hp := weight_pos C
      omega) u
  have he : weight ((C.getD u []).getD v 0)≤ weight (C.getD u []) :=
    getD_weight (C.getD u []) 0 (by
      change 1≤ weight (C.getD u [])
      exact weight_pos _) v
  exact he.trans hr

lemma updateCell_weight (z : EntryInput) :
    weight (updateCell z)≤8*weight z.1.1.1+3 := by
  have hb := updateCell_bounds z
  have h1 := weight_nat_small hb.1
  have h2 := weight_nat_small hb.2
  have hc1 := capacityEntry_weight z.1.1.1 z.2.1 z.2.2
  have hc2 := capacityEntry_weight z.1.1.1 z.2.2 z.2.1
  change weight ((updateCell z).1,(updateCell z).2)≤_
  rw [weight_prod]
  change weight (updateCell z).1≤4*weight (capacityEntry (z.1.1.1,(z.2.1,z.2.2)))+1 at h1
  change weight (updateCell z).2≤
    4*weight (capacityEntry (z.1.1.1,(z.2.2,z.2.1)))+1 at h2
  omega

lemma updateRow_weight (z : FlowEntryProgram.UpdateData×ℕ) :
    weight (updateRow z)≤ z.1.1.1.length*(8*weight z.1.1.1+4)+1 := by
  have h := weight_map_bound (as:=List.range z.1.1.1.length)
    (f:=fun v=>updateCell (z.1,(z.2,v))) (N:=8*weight z.1.1.1+3)
    (fun v _=>updateCell_weight (z.1,(z.2,v)))
  simpa only [updateRow,List.length_range] using h

lemma updateMatrix_weight (z : FlowEntryProgram.UpdateData) :
    weight (updateMatrix z)≤ z.1.1.length*(z.1.1.length*(8*weight z.1.1+4)+2)+1 := by
  have h := weight_map_bound (as:=List.range z.1.1.length)
    (f:=fun u=>updateRow (z,u)) (N:=z.1.1.length*(8*weight z.1.1+4)+1)
    (fun u _=>updateRow_weight (z,u))
  simpa only [updateMatrix,List.length_range] using h

def matrixBound (C : NatMatrix) : ℕ := C.length*(C.length*(8*weight C+4)+2)+1

lemma augment_weight (z : Data×List ℕ) : weight (augment z)≤ matrixBound z.1.1 := by
  exact updateMatrix_weight (prepareAugment z)

lemma advance_weight (z : Data×(ℕ×ℕ)) :
    weight (advance z)≤ max (weight z.1.2) (matrixBound z.1.1) := by
  cases hs : ResidualGraphProgram.search z with
  | none => simpa only [advance,hs] using le_max_left (weight z.1.2) (matrixBound z.1.1)
  | some xs =>
    simpa only [advance,hs] using (augment_weight (z.1,xs)).trans
      (le_max_right (weight z.1.2) (matrixBound z.1.1))

lemma matrixBound_le {S : ℕ} (C : NatMatrix) (h : weight C≤ S) :
    matrixBound C≤8*S^3+4*S^2+2*S+1 := by
  have hn : C.length≤ S := (list_length_le_weight C).trans h
  have h1 := Nat.mul_le_mul hn (show 8*weight C+4≤8*S+4 by omega)
  have h2 := Nat.mul_le_mul hn (show C.length*(8*weight C+4)+2≤ S*(8*S+4)+2 by omega)
  unfold matrixBound
  nlinarith

end ContingencyTables.FlowMatrixBounds

end OAI
