import Mathlib
import OAI.Analysis.LaughlinFock.FourLie

namespace OAI

/-! Four Copies. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

abbrev FourSpinIndex (Q : ℕ) := (r : CopyLabel Q) × Fin (2*Q-2*r.val.val+1)

 

abbrev ValidFourCopy (Q : ℕ) :=
  {b : (D : Fin (2*Q)) × CopyLabel D.val // b.1.val + b.2.val.val ≤ 2*Q}

 
def fourSpinCopyEquiv {Q : ℕ} (_hQ : 1 ≤ Q) : FourSpinIndex Q ≃ ValidFourCopy Q where
  toFun b := by
    have hr := b.1.val.isLt
    have hz := b.2.isLt
    have hr0 := b.1.property.pos
    refine ⟨⟨⟨b.1.val.val+b.2.val, by omega⟩,
      ⟨⟨b.1.val.val, by dsimp; omega⟩, b.1.property⟩⟩, ?_⟩
    dsimp
    omega
  invFun b := by
    have hr := b.val.2.val.isLt
    have hd := b.property
    have hr0 := b.val.2.property.pos
    refine ⟨⟨⟨b.val.2.val.val, by omega⟩, b.val.2.property⟩,
      ⟨b.val.1.val-b.val.2.val.val, ?_⟩⟩
    dsimp only
    omega
  left_inv b := by
    apply Sigma.ext
    · apply Subtype.ext
      apply Fin.ext
      rfl
    · apply (Fin.heq_ext_iff rfl).mpr
      dsimp
      omega
  right_inv b := by
    rcases b with ⟨⟨⟨D,hD⟩,⟨⟨r,hr⟩,hor⟩⟩,h⟩
    have he : r+(D-r)=D := by dsimp only at hr; omega
    apply Subtype.ext
    dsimp
    have hs {d e : Fin (2*Q)} (u : CopyLabel d.val) (v : CopyLabel e.val)
        (hde : d=e) (huv : u.val.val=v.val.val) : (⟨d,u⟩ : (D : Fin (2*Q)) × CopyLabel D.val) = ⟨e,v⟩ := by
      subst e
      congr 1
      exact Subtype.ext (Fin.ext huv)
    exact hs _ _ (Fin.ext he) rfl

 
def fourSpinDegree (Q D : ℕ) : ℕ := 4*Q-2-2*D

 

def fourCopyColumns (Q D : ℕ) (r : CopyLabel D) :
    Matrix (FourUncoupled Q) (Fin (fourSpinDegree Q D+1)) ℂ :=
  if D+r.val.val ≤ 2*Q then
    fun b k => (composedCoupledVector Q r.val.val (D-r.val.val) k.val b : ℂ)
  else 0

 
def fourSpinColumns (Q : ℕ) (b : FourSpinIndex Q) :
    Matrix (FourUncoupled Q)
      (Fin ((2*Q-2)+(2*Q-2*b.1.val.val)-2*b.2.val+1)) ℂ :=
  fun x k => (composedCoupledVector Q b.1.val.val b.2.val k.val x : ℂ)

 
theorem fourSpinColumns_eq_copy {Q : ℕ} (hQ : 1 ≤ Q) (b : FourSpinIndex Q) :
    fourSpinColumns Q b =
      (fourCopyColumns Q (fourSpinCopyEquiv hQ b).val.1.val
        (fourSpinCopyEquiv hQ b).val.2).submatrix id (Fin.cast (by
          have := b.1.val.isLt
          have := b.2.isLt
          have := b.1.property.pos
          dsimp [fourSpinDegree, fourSpinCopyEquiv]
          omega)) := by
  have hd := (fourSpinCopyEquiv hQ b).property
  rw [fourCopyColumns]
  erw [ite_eq_left hd]
  ext x k
  simp only [fourSpinCopyEquiv, Equiv.coe_fn_mk, fourSpinColumns, Nat.add_sub_cancel_left]
  rfl

 
def fourCopyWedge (Q D : ℕ) (r : CopyLabel D) :
    Matrix (SectorOccupation Q 4) (Fin (fourSpinDegree Q D+1)) ℂ :=
  wideFourWedgeMatrix Q * fourCopyColumns Q D r

 

theorem fourCopyWedge_intertwines {Q D : ℕ} (hQ : 1 ≤ Q) (r : CopyLabel D) (s : Fin 3) :
    sectorOneBody Q 4 (spinGenerator Q s)*fourCopyWedge Q D r =
      fourCopyWedge Q D r*spinGenerator (fourSpinDegree Q D) s := by
  by_cases hd : D+r.val.val ≤ 2*Q
  · have hr := r.val.isLt
    have hr0 := r.property.pos
    have he : (2*Q-2)+(2*Q-2*r.val.val)-2*(D-r.val.val) = fourSpinDegree Q D := by
      dsimp [fourSpinDegree]
      omega
    have hw : fourCopyWedge Q D r =
        (fourSpinWedge Q r.val.val (D-r.val.val)).submatrix id
          (Fin.cast (congrArg (·+1) he.symm)) := by
      rw [fourCopyWedge, fourCopyColumns]
      erw [ite_eq_left hd]
      ext S k
      simp only [Matrix.submatrix_apply, id_eq, Fin.val_cast, fourSpinWedge,
        composedFourWedgeColumn, Matrix.mulVec, dotProduct]
      rfl
    rw [hw]
    have hi := fourSpinWedge_intertwines hQ (by omega : r.val.val ≤ Q) r.property
      (by omega : D-r.val.val ≤ 2*Q-2) (by omega : D-r.val.val ≤ 2*Q-2*r.val.val) s
    have hc (n m : ℕ) (he : n=m)
        (C : Matrix (SectorOccupation Q 4) (Fin (n+1)) ℂ)
        (hi : sectorOneBody Q 4 (spinGenerator Q s)*C = C*spinGenerator n s) :
        sectorOneBody Q 4 (spinGenerator Q s)*C.submatrix id (Fin.cast (congrArg (·+1) he.symm)) =
          C.submatrix id (Fin.cast (congrArg (·+1) he.symm))*spinGenerator m s := by
      subst m
      simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hi
    exact hc _ _ he _ hi
  · simp [fourCopyWedge, fourCopyColumns, hd]

end LaughlinFock
end

end OAI
