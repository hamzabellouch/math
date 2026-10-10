import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListPartition

namespace OAI

/-! The compiler's prefix sums enumerate precisely the actual pairs. The
result fixes which two fresh spins belong to each center and local pair. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList

theorem pairStart_zero (gs : Groups) : pairStart gs 0=0 := rfl

theorem pairStart_cons_succ (ps : List Port) (gs : Groups) (i : ℕ) :
    pairStart (ps::gs) (i+1)=ps.length/2+pairStart gs i := by
  simp only [pairStart,List.take_succ_cons,pairCount_cons]

theorem pairStart_bound (gs : Groups) (i : ℕ) (hi : i < gs.length) :
    pairStart gs i+(groupAt gs i).length/2 ≤ pairCount gs := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons ps gs ih =>
    cases i with
    | zero => simp only [pairStart_zero,zero_add,groupAt_cons_zero,pairCount_cons]; omega
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      rw [pairStart_cons_succ,groupAt_cons_succ,pairCount_cons]
      have := ih i hi'
      omega

theorem pair_index_lt (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) : pairStart gs i+j < pairCount gs := by
  have := pairStart_bound gs i hi
  omega

theorem pairs_getElem? (ps : List Port) (j : ℕ) (hj : j < ps.length/2) :
    (pairs ps)[j]?=some (portAt ps (2*j),portAt ps (2*j+1)) := by
  rw [List.getElem?_eq_getElem (by simpa only [pairs_length] using hj)]
  simp only [pairs,List.getElem_map,List.getElem_range]

theorem catalog_getElem? (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    (catalog gs)[pairStart gs i+j]? =
      some (i,(portAt (groupAt gs i) (2*j),portAt (groupAt gs i) (2*j+1))) := by
  induction gs generalizing i with
  | nil => simp at hi
  | cons ps gs ih =>
    cases i with
    | zero =>
      rw [catalog_cons,pairStart_zero,zero_add,
        List.getElem?_append_left (by simpa only [List.length_map,pairs_length,
          groupAt_cons_zero] using hj),List.getElem?_map]
      rw [groupAt_cons_zero] at hj ⊢
      rw [pairs_getElem? ps j hj]
      rfl
    | succ i =>
      have hi' : i < gs.length := by simpa using hi
      rw [groupAt_cons_succ] at hj ⊢
      rw [catalog_cons,pairStart_cons_succ,
        List.getElem?_append_right (by simp only [List.length_map,pairs_length]; omega),
        List.length_map,pairs_length]
      have he : ps.length/2+pairStart gs i+j-ps.length/2=pairStart gs i+j := by omega
      rw [he,List.getElem?_map,ih i hi' hj]
      rfl

theorem catalog_headD (gs : Groups) (i j : ℕ) (hi : i < gs.length)
    (hj : j < (groupAt gs i).length/2) :
    ((catalog gs).drop (pairStart gs i+j)).headD (0,((0,0),(0,0))) =
      (i,(portAt (groupAt gs i) (2*j),portAt (groupAt gs i) (2*j+1))) := by
  rw [List.headD_eq_head?_getD,List.head?_drop,catalog_getElem? gs i j hi hj]
  rfl

end ContinuumCoulomb.QuantumForkList

end

end OAI
