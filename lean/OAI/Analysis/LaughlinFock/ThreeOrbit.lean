import Mathlib
import OAI.Analysis.LaughlinFock.PairOrbit

namespace OAI

/-! Three Orbit. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def threeSpinColumns (Q z : ℕ) :
    Matrix (PairLabel Q × Orbital Q) (Fin (2*Q-2+Q-2*z+1)) ℂ :=
  fun pj k => threeCoupledColumn Q z k.val pj

 

theorem threeSpinProjection_columns {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinProjection Q z = threeSpinColumns Q z * (threeSpinColumns Q z)ᴴ := by
  classical
  let r : Fin (min (2*Q-2) Q+1) := ⟨z, by omega⟩
  ext i j
  unfold threeSpinProjection
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, threeCouplingMatrix,
    mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · simp only [r, ite_true]
    rfl
  · intro a _ ha
    have han : a.val ≠ z := by
      intro h; apply ha; exact Fin.ext h
    simp only [ite_eq_right han, Finset.sum_const_zero]
  · simp

 
def threeSpinWedge (Q z : ℕ) :
    Matrix (SectorOccupation Q 3) (Fin (2*Q-2+Q-2*z+1)) ℂ :=
  threeWedgeMatrix Q * threeSpinColumns Q z

 

theorem threeSpinWedge_eq_tensor {Q : ℕ} (hQ : 1 ≤ Q) (z : ℕ) :
    threeSpinWedge Q z =
      wedgeProductMatrix Q 2 1 (pairSpinMatrix Q) (oneParticleMatrix Q) *
        coupledSpinMatrix (2*Q-2) Q z := by
  classical
  let e : (Fin (2*Q-2+1) × Orbital Q) ≃ (PairLabel Q × Orbital Q) :=
    Equiv.prodCongr (finCongr (by omega)) (Equiv.refl _)
  ext S k
  change (∑ pj, threeWedgeMatrix Q S pj * threeCoupledColumn Q z k.val pj) = _
  rw [← e.sum_comp (fun pj => threeWedgeMatrix Q S pj * threeCoupledColumn Q z k.val pj)]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro pj _
  have hv : (fun T => wedgeProductMatrix Q 2 1 (pairSpinMatrix Q) (oneParticleMatrix Q) T pj) =
      (fun T => threeWedgeMatrix Q T (e pj)) := by
    apply wedgeAnnihilator_injective Q 3
    rw [wedgeProductMatrix_contraction Q 2 1, oneParticleMatrix_contraction,
      threeWedgeMatrix_annihilator_column]
    simp only [pairSpinMatrix, pairVector,
      wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _)]
    rfl
  rw [congrFun hv S]
  rfl

 
theorem threeSpinWedge_intertwines {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) (s : Fin 3) :
    sectorOneBody Q 3 (spinGenerator Q s) * threeSpinWedge Q z =
      threeSpinWedge Q z * spinGenerator (2*Q-2+Q-2*z) s := by
  rw [threeSpinWedge_eq_tensor (by omega)]
  rw [← Matrix.mul_assoc,
    wedgeProductMatrix_intertwines Q 2 1 _ (spinGenerator_skew Q s) _ _ _ _
      (pairSpinMatrix_intertwines (by omega) s)
      (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s)),
    Matrix.mul_assoc, coupledSpinMatrix_intertwines (by omega : z ≤ 2*Q-2) hz,
    Matrix.mul_assoc]

 
theorem threeSpinWedge_gram {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    threeSpinWedge Q z * (threeSpinWedge Q z)ᴴ =
      threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ := by
  rw [threeSpinProjection_columns hQ hz, threeSpinWedge, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

 

theorem fockAverage_highestThree {Q z : ℕ} (hQ : 2 ≤ Q) (hz : z ≤ Q) :
    fockAverage Q ((highestThreeAnnihilator Q z hz)ᴴ * highestThreeAnnihilator Q z hz) =
      (1 / ((3*Q-1-2*z : ℕ) : ℂ)) •
        exteriorLift Q 3 (threeWedgeMatrix Q * threeSpinProjection Q z * (threeWedgeMatrix Q)ᴴ) := by
  have h := fockAverage_spin_column (threeSpinWedge Q z) (threeSpinWedge_intertwines hQ hz)
    (⟨0,by omega⟩ : Fin (2*Q-2+Q-2*z+1))
  have hc : (fun A => threeSpinWedge Q z A (⟨0,by omega⟩ : Fin (2*Q-2+Q-2*z+1))) =
      threeWedgeMatrix Q *ᵥ threeCoupledColumn Q z 0 := rfl
  rw [hc, ← highestThreeAnnihilator_eq_wedge hQ hz, threeSpinWedge_gram hQ hz] at h
  have hd : ((2*Q-2+Q-2*z : ℕ) : ℂ)+1 = ((3*Q-1-2*z : ℕ) : ℂ) := by
    rw [← Nat.cast_add_one]
    congr 1
    omega
  simpa only [hd] using h

end LaughlinFock
end

end OAI
