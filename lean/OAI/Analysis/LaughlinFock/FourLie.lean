import Mathlib
import OAI.Analysis.LaughlinFock.PairLie

namespace OAI

/-! Four Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
def oddPairSpinMatrix (Q r : ℕ) :
    Matrix (SectorOccupation Q 2) (Fin (2*Q-2*r+1)) ℂ :=
  fun S k => wedgeCoupledCoefficient Q r k.val ((increasingPairEquiv Q).symm S)

theorem oddPairSpinMatrix_contraction (Q r : ℕ) (k : Fin (2*Q-2*r+1)) :
    wedgeAnnihilator Q 2 (fun S => oddPairSpinMatrix Q r S k) =
      (Real.sqrt 2 : ℂ) • coefficientPairAnnihilator Q
        (fun i j => (coupledVector Q Q r k.val i.val j.val : ℂ)) := by
  classical
  rw [coefficientPair_basis_expansion, Finset.smul_sum]
  unfold wedgeAnnihilator
  rw [← (increasingPairEquiv Q).sum_comp]
  apply Finset.sum_congr rfl
  intro ij _
  have hi : (increasingPairEquiv Q).symm (increasingPairSector Q ij) = ij :=
    (increasingPairEquiv Q).symm_apply_apply ij
  simp only [oddPairSpinMatrix, increasingPairEquiv_apply, hi, wedgeCoupledCoefficient,
    Complex.ofReal_mul, star_mul, Complex.star_def, Complex.conj_ofReal, smul_smul, mul_comm]

 

theorem tensorWedge_oddPairSpinMatrix {Q r : ℕ} (hr : r ≤ Q) (hor : Odd r) :
    wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
        coupledSpinMatrix Q Q r =
      (Real.sqrt 2 : ℂ) •
        (oddPairSpinMatrix Q r).submatrix id (Fin.cast (by omega)) := by
  ext S k
  have hv : wedgeAnnihilator Q 2
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ
        (fun ij => coupledSpinMatrix Q Q r ij k)) =
      wedgeAnnihilator Q 2 ((Real.sqrt 2 : ℂ) •
        fun T => oddPairSpinMatrix Q r T (Fin.cast (by omega) k)) := by
    rw [tensorWedge_contraction]
    · rw [wedgeAnnihilator_smul]
      rw [oddPairSpinMatrix_contraction Q r (Fin.cast (by omega) k)]
      rw [smul_smul]
      simp only [Complex.star_def, Complex.conj_ofReal, coupledSpinMatrix, Fin.val_cast]
      have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
        exact_mod_cast (Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2))
      rw [hs]
    · intro i j
      dsimp [coupledSpinMatrix]
      rw [coupledVector_antisymm hr hor]
      simp
  exact congrFun (wedgeAnnihilator_injective Q 2 hv) S

 
theorem oddPairSpinMatrix_intertwines {Q r : ℕ} (hr : r ≤ Q) (hor : Odd r) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) * oddPairSpinMatrix Q r =
      oddPairSpinMatrix Q r * spinGenerator (2*Q-2*r) s := by
  have he : sectorOneBody Q 2 (spinGenerator Q s) *
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q r) =
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q r) *
      spinGenerator (Q+Q-2*r) s := by
    rw [← Matrix.mul_assoc, tensorWedge_intertwines, Matrix.mul_assoc,
      coupledSpinMatrix_intertwines hr hr, Matrix.mul_assoc]
  rw [tensorWedge_oddPairSpinMatrix hr hor] at he
  simp only [Matrix.mul_smul, Matrix.smul_mul] at he
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hf := smul_right_injective _ hn he
  have hc (n : ℕ) (e : n = 2*Q-2*r)
      (hc : sectorOneBody Q 2 (spinGenerator Q s) *
          (oddPairSpinMatrix Q r).submatrix id (Fin.cast (congrArg (·+1) e)) =
        (oddPairSpinMatrix Q r).submatrix id (Fin.cast (congrArg (·+1) e)) * spinGenerator n s) :
      sectorOneBody Q 2 (spinGenerator Q s) * oddPairSpinMatrix Q r =
        oddPairSpinMatrix Q r * spinGenerator (2*Q-2*r) s := by
    subst n
    simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hc
  exact hc _ (by omega) hf

 
def fourSpinWedge (Q r z : ℕ) :
    Matrix (SectorOccupation Q 4) (Fin ((2*Q-2)+(2*Q-2*r)-2*z+1)) ℂ :=
  fun S k => composedFourWedgeColumn Q r z k.val S

 
theorem oddPairSpinMatrix_contraction_increasing (Q r : ℕ) (k : Fin (2*Q-2*r+1)) :
    wedgeAnnihilator Q 2 (fun S => oddPairSpinMatrix Q r S k) =
      ∑ ij : IncreasingPair Q, (wedgeCoupledCoefficient Q r k.val ij : ℂ) •
        (annihilator Q ij.val.2 * annihilator Q ij.val.1) := by
  rw [oddPairSpinMatrix_contraction, coefficientPair_basis_expansion, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [show (increasingPairSector Q ij).val = {ij.val.1,ij.val.2} from rfl,
    basisAnnihilator_pair _ _ ij.property, smul_smul]
  simp only [wedgeCoupledCoefficient, Complex.ofReal_mul]

 

theorem fourSpinWedge_eq_tensor (Q r z : ℕ) :
    fourSpinWedge Q r z =
      wedgeProductMatrix Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) *
        coupledSpinMatrix (2*Q-2) (2*Q-2*r) z := by
  ext S k
  have hv : wedgeAnnihilator Q 4 (composedFourWedgeColumn Q r z k.val) =
      wedgeAnnihilator Q 4
        (wedgeProductMatrix Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) *ᵥ
          fun b => coupledSpinMatrix (2*Q-2) (2*Q-2*r) z b k) := by
    rw [← composedFourAnnihilator_eq_wedge, wedgeAnnihilator_mulVec]
    have hh (b : Fin (2*Q-2+1) × Fin (2*Q-2*r+1)) :=
      wedgeProductMatrix_contraction Q 2 2 (pairSpinMatrix Q) (oddPairSpinMatrix Q r) b
    have ho (a : Fin (2*Q-2*r+1)) := oddPairSpinMatrix_contraction_increasing Q r a
    simp only [hh, ho,
      pairSpinMatrix, pairVector,
      wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
      coupledSpinMatrix, Complex.star_def, Complex.conj_ofReal,
      composedFourAnnihilator, composedCoupledVector, Fintype.sum_prod_type,
      Complex.ofReal_sum, Finset.sum_smul, Complex.ofReal_mul,
      Matrix.sum_mul, Matrix.smul_mul, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  exact congrFun (wedgeAnnihilator_injective Q 4 hv) S

 

theorem fourSpinWedge_intertwines {Q r z : ℕ} (hQ : 1 ≤ Q)
    (hr : r ≤ Q) (hor : Odd r) (hz₁ : z ≤ 2*Q-2) (hz₂ : z ≤ 2*Q-2*r) (s : Fin 3) :
    sectorOneBody Q 4 (spinGenerator Q s) * fourSpinWedge Q r z =
      fourSpinWedge Q r z * spinGenerator ((2*Q-2)+(2*Q-2*r)-2*z) s := by
  rw [fourSpinWedge_eq_tensor]
  rw [← Matrix.mul_assoc,
    wedgeProductMatrix_intertwines Q 2 2 _ (spinGenerator_skew Q s) _ _ _ _
      (pairSpinMatrix_intertwines hQ s) (oddPairSpinMatrix_intertwines hr hor s),
    Matrix.mul_assoc, coupledSpinMatrix_intertwines hz₁ hz₂, Matrix.mul_assoc]

end LaughlinFock
end

end OAI
