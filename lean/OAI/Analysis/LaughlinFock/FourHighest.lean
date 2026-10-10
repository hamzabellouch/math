import Mathlib
import OAI.Analysis.LaughlinFock.FourTrace

namespace OAI

/-! Four Highest. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem exteriorLift_mixed_single {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Q k : ℕ)
    (C : Matrix (SectorOccupation Q k) ι ℂ) (D : Matrix (SectorOccupation Q k) κ ℂ)
    (p : ι) (q : κ) :
    exteriorLift Q k (C*Matrix.single p q (1 : ℂ)*Dᴴ) =
      (wedgeAnnihilator Q k (fun A => C A p))ᴴ *
        wedgeAnnihilator Q k (fun A => D A q) := by
  have h : C*Matrix.single p q (1 : ℂ)*Dᴴ =
      Matrix.vecMulVec (fun A => C A p) (star (fun A => D A q)) := by
    ext A B
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Matrix.vecMulVec_apply]
  rw [h, exteriorLift_rankOne]

 

theorem fockAverage_spin_mixed_column {Q k n : ℕ}
    (C D : Matrix (SectorOccupation Q k) (Fin (n+1)) ℂ)
    (hC : ∀ s, sectorOneBody Q k (spinGenerator Q s)*C = C*spinGenerator n s)
    (hD : ∀ s, sectorOneBody Q k (spinGenerator Q s)*D = D*spinGenerator n s)
    (p : Fin (n+1)) :
    fockAverage Q ((wedgeAnnihilator Q k (fun A => C A p))ᴴ *
      wedgeAnnihilator Q k (fun A => D A p)) =
      (1/(n+1 : ℂ)) • exteriorLift Q k (C*Dᴴ) := by
  rw [← exteriorLift_mixed_single Q k C D p p,
    fockAverage_spin_mixed_sandwich C D hC hD, Matrix.trace_single_eq_same]

 

theorem fourCopyWedge_column {Q D : ℕ} (hr : D ≤ Q) (r : CopyLabel D)
    (k : Fin (fourSpinDegree Q D+1)) :
    (fun A => fourCopyWedge Q D r A k) =
      composedFourWedgeColumn Q r.val.val (D-r.val.val) k.val := by
  have hrl := r.val.isLt
  unfold fourCopyWedge fourCopyColumns
  erw [ite_eq_left (by omega : D+r.val.val ≤ 2*Q)]
  rfl

 
theorem fockAverage_highestFour {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q)
    (r s : CopyLabel D) :
    fockAverage Q ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s) =
      (1/(fourSpinDegree Q D+1 : ℂ)) • fourCopyLift Q D r s := by
  have h := fockAverage_spin_mixed_column (fourCopyWedge Q D r) (fourCopyWedge Q D s)
    (fourCopyWedge_intertwines hQ r) (fourCopyWedge_intertwines hQ s)
    (⟨0, by omega⟩ : Fin (fourSpinDegree Q D+1))
  rw [fourCopyWedge_column hD, fourCopyWedge_column hD,
    ← highestFourAnnihilator_eq_wedge hD r, ← highestFourAnnihilator_eq_wedge hD s] at h
  exact h

 
theorem exteriorLift_mixed_gram {ι : Type*} [Fintype ι]
    (Q k : ℕ) (C D : Matrix (SectorOccupation Q k) ι ℂ) :
    exteriorLift Q k (C*Dᴴ) = ∑ p,
      (wedgeAnnihilator Q k (fun A => C A p))ᴴ *
        wedgeAnnihilator Q k (fun A => D A p) := by
  have h : C*Dᴴ = ∑ p, Matrix.vecMulVec (fun A => C A p) (star (fun A => D A p)) := by
    ext A B
    simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply]
  rw [h, exteriorLift_sum]
  simp only [exteriorLift_rankOne]

 
theorem fourCopyLift_eq_weights {Q D : ℕ} (hD : D ≤ Q) (r s : CopyLabel D) :
    fourCopyLift Q D r s = ∑ k : Fin (fourSpinDegree Q D+1),
      (composedFourAnnihilator Q r.val.val (D-r.val.val) k.val)ᴴ *
        composedFourAnnihilator Q s.val.val (D-s.val.val) k.val := by
  rw [fourCopyLift, exteriorLift_mixed_gram]
  simp only [fourCopyWedge_column hD, ← composedFourAnnihilator_eq_wedge]

 
def firstFourCopy {D : ℕ} (hD : 1 ≤ D) : CopyLabel D := ⟨⟨1,by omega⟩, by change Odd (1:ℕ); decide⟩

 

theorem targetCopy_sum {Q D : ℕ} (hD : 1 ≤ D) (f : CopyLabel D → CopyLabel D → FockMatrix Q) :
    (∑ r, ∑ s, targetCopy D r s • f r s) = f (firstFourCopy hD) (firstFourCopy hD) := by
  classical
  have he (r : CopyLabel D) : r.val.val=1 ↔ r=firstFourCopy hD := by
    constructor
    · intro h
      exact Subtype.ext (Fin.ext h)
    · rintro rfl
      rfl
  simp [targetCopy, he, ite_and, ite_smul]

 

theorem fourCopyLift_first {Q D : ℕ} (hQ : 1 ≤ Q) (hD : 1 ≤ D) (hd : D ≤ Q) :
    fourCopyLift Q D (firstFourCopy hD) (firstFourCopy hD) =
      ∑ k ∈ Finset.range (fourSpinDegree Q D+1),
        (fourCoupledAnnihilator Q (D-1) k)ᴴ * fourCoupledAnnihilator Q (D-1) k := by
  rw [fourCopyLift_eq_weights hd]
  simp only [firstFourCopy, composedFourAnnihilator_one hQ]
  exact Fin.sum_univ_eq_sum_range (fun k =>
    (fourCoupledAnnihilator Q (D-1) k)ᴴ * fourCoupledAnnihilator Q (D-1) k) _

end LaughlinFock
end

end OAI
