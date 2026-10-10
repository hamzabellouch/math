import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.MediatorListProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceMatrix

namespace OAI

/-! The concrete TM2 bond lists are exactly the enumerations of the finite
spin matrices whose three-stage bottom-energy estimates were proved. -/

namespace ContinuumCoulomb.MediatorIteration
open MediatorGraph

abbrev Bond := MediatorListProgram.Bond

def Bonds.toList {n r : ℕ} (F : Bonds n r) : List Bond :=
  List.ofFn (fun e => ((F.left e).val, (F.right e).val, F.weight e))

@[simp] theorem Bonds.toList_length {n r : ℕ} (F : Bonds n r) : F.toList.length = r := by
  simp only [Bonds.toList, List.length_ofFn]

theorem Bonds.toList_get {n r : ℕ} (F : Bonds n r) (i : ℕ) (hi : i < r) :
    (F.toList.drop i).headD MediatorListProgram.zeroBond =
      ((F.left ⟨i, hi⟩).val, (F.right ⟨i, hi⟩).val, F.weight ⟨i, hi⟩) := by
  simp only [List.headD_eq_head?_getD, List.head?_drop]
  rw [List.getElem?_eq_getElem (by simpa using hi)]
  simp only [Option.getD_some, Bonds.toList, List.getElem_ofFn]

theorem old_val (n r : ℕ) (i : Fin n) : (old n r i).val = i.val := rfl

theorem fresh_val (n r : ℕ) (e : Fin r) (s : Fin 2) :
    (fresh n r e s).val = n + 2 * e.val + s.val := by
  change n + (s.val + 2 * e.val) = _
  omega

theorem lift_toList {n q : ℕ} (r : ℕ) (F : Bonds n q) : (lift r F).toList = F.toList := by
  unfold Bonds.toList
  congr 1

theorem join_toList {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) :
    (join F K).toList = F.toList ++ K.toList := by
  unfold Bonds.toList
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext e
    change ((join F K).left (Fin.castAdd r e) |>.val,
      (join F K).right (Fin.castAdd r e) |>.val, (join F K).weight (Fin.castAdd r e)) = _
    simp only [join, finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
  · congr 1
    funext e
    simp only [join, finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]

theorem central_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (central n r (MediatorParameters.delta r W G : ℚ)).toList =
      MediatorListProgram.central ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp [MediatorListProgram.central]
  · intro i hi hj
    simp only [Bonds.toList, List.getElem_ofFn, MediatorListProgram.central,
      List.getElem_map, List.getElem_range, central, fresh_val, Fin.val_zero, Fin.val_one, add_zero]

theorem spokes_toList_input {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))).toList =
      MediatorListProgram.spokes ((r, W, G, n), F.toList) := by
  apply List.ext_getElem
  · simp only [Bonds.toList_length, MediatorListProgram.spokes, List.length_map,
      List.length_range]
    omega
  · intro i hi hj
    have hir : i < r * 2 := by simpa only [Bonds.toList_length] using hi
    have hdiv : i / 2 < r := by omega
    let S := spokes F (fun e => member (F.weight e))
      (fun e => MediatorParameters.spoke r W G (F.weight e))
    change (List.ofFn (fun e => ((S.left e).val, (S.right e).val, S.weight e)))[i]'(by
      simpa only [List.length_ofFn] using hir) = _
    rw [List.getElem_ofFn]
    simp only [MediatorListProgram.spokes, List.getElem_map, List.getElem_range]
    rw [Bonds.toList_get F (i / 2) hdiv]
    dsimp only [S]
    simp only [spokes, MediatorListProgram.spoke, old_val, fresh_val]
    change ( (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then
        F.left ((⟨i, hir⟩ : Fin (r * 2)).divNat) else F.right ((⟨i, hir⟩ : Fin (r * 2)).divNat)).val,
      n + 2 * (i / 2) +
        (if (⟨i, hir⟩ : Fin (r * 2)).modNat = 0 then (0 : Fin 2) else member (F.weight ⟨i / 2, hdiv⟩)).val,
      MediatorParameters.spoke r W G (F.weight ⟨i / 2, hdiv⟩)) = _
    have hmod : (⟨i, hir⟩ : Fin (r * 2)).modNat = (0 : Fin 2) ↔ i % 2 = 0 := by
      exact Fin.ext_iff
    by_cases hm : i % 2 = 0
    · simp only [hm, hmod.mpr hm, ite_true, Fin.val_zero]
      rfl
    · simp only [hm, ite_false, (not_congr hmod).mpr hm, member]
      split <;> rfl

end ContinuumCoulomb.MediatorIteration

end OAI
