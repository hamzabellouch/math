import OAI.Combinatorics.ContingencyTables.Dense.DenseAxisProposal
import OAI.Combinatorics.ContingencyTables.Dense.GridMetropolis
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI

/-! # Exact proposal frequencies from a bounded fair-bit integer -/

namespace ContingencyTables.GridBoundary

open scoped Classical

def directionCodeEquiv (q : ℕ) : Fin q × Bool ≃ Fin (q * 2) :=
  (Equiv.prodCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finProdFinEquiv

def axisCodeStep {q K M : ℕ} (a : Grid (I := Fin q) K) (z : Fin M) :
    Option (Grid (I := Fin q) K) :=
  if hz : z.val < q * 2 then
    let dir := (directionCodeEquiv q).symm ⟨z.val, hz⟩
    axisStep a dir.1 dir.2
  else none

theorem axisCodeStep_sound {q K M : ℕ} (a b : Grid (I := Fin q) K) (z : Fin M)
    (h : axisCodeStep a z = some b) : Neighbor a b := by
  unfold axisCodeStep at h
  split_ifs at h with hz
  exact ⟨_, _, axisStep_sound _ _ _ _ h⟩

theorem axisCodeStep_unique {q K M : ℕ} (a b : Grid (I := Fin q) K)
    (z z' : Fin M) (h : axisCodeStep a z = some b) (h' : axisCodeStep a z' = some b) : z = z' := by
  unfold axisCodeStep at h h'
  split_ifs at h with hz
  split_ifs at h' with hz'
  have hd := oriented_direction_unique a b _ _ _ _
    (axisStep_sound _ _ _ _ h) (axisStep_sound _ _ _ _ h')
  have he := congrArg (directionCodeEquiv q) hd
  have he' : (⟨z.val, hz⟩ : Fin (q * 2)) = ⟨z'.val, hz'⟩ := by
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using he
  exact Fin.ext (congrArg (fun x : Fin (q * 2) => x.val) he')

theorem axisCodeStep_exists {q K M : ℕ} (hM : q * 2 ≤ M)
    (a b : Grid (I := Fin q) K) (h : Neighbor a b) :
    ∃ z : Fin M, axisCodeStep a z = some b := by
  obtain ⟨i, sign, hi⟩ := h
  let dir := directionCodeEquiv q (i, sign)
  let z : Fin M := ⟨dir.val, dir.isLt.trans_le hM⟩
  refine ⟨z, ?_⟩
  unfold axisCodeStep
  have hz : z.val < q * 2 := dir.isLt
  rw [dite_eq_left hz]
  change axisStep a ((directionCodeEquiv q).symm dir).1
    ((directionCodeEquiv q).symm dir).2 = some b
  rw [Equiv.symm_apply_apply]
  exact axisStep_complete a b i sign hi

/-- Every valid signed direction has exactly one fair-bit integer code;
all unused codes and boundary steps are rejected. -/
theorem axisCodeStep_count {q K M : ℕ} (hM : q * 2 ≤ M)
    (a b : Grid (I := Fin q) K) :
    (Finset.univ.filter (fun z : Fin M => axisCodeStep a z = some b)).card =
      if Neighbor a b then 1 else 0 := by
  by_cases hab : Neighbor a b
  · rw [ite_eq_left hab, Finset.card_eq_one_iff_existsUnique]
    obtain ⟨z, hz⟩ := axisCodeStep_exists hM a b hab
    refine ⟨z, by simpa, ?_⟩
    intro z' hz'
    exact axisCodeStep_unique a b z' z (by simpa using hz') hz
  · rw [ite_eq_right hab, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hab (axisCodeStep_sound a b z (by simpa using hz))

theorem dense_proposal_code_bound (d q : ℕ) (hq : q ≤ d) :
    q * 2 ≤ 2 ^ Nat.clog 2 (8 * d) := by
  exact (by omega : q * 2 ≤ 8 * d).trans (Nat.le_pow_clog (by decide) (8 * d))

end ContingencyTables.GridBoundary

end OAI
