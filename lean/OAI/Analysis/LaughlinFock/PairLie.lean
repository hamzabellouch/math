import Mathlib
import OAI.Analysis.LaughlinFock.CoupledLie

namespace OAI

/-! Pair Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 
theorem wedgeAnnihilator_smul (Q k : ℕ) (c : ℂ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k (c • v) = star c • wedgeAnnihilator Q k v := by
  unfold wedgeAnnihilator
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S _
  change (star (c * v S)) • basisAnnihilator Q S.val = _
  rw [star_mul, smul_smul, mul_comm]

 
theorem symmetric_sum_upper {ι V : Type*} [Fintype ι] [LinearOrder ι]
    [AddCommMonoid V] (f : ι → ι → V)
    (hsymm : ∀ i j, f j i = f i j) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) =
      (∑ i, ∑ j, if i < j then f i j else 0) + ∑ i, ∑ j, if i < j then f i j else 0 := by
  have ht (i j : ι) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le, hsymm]
  calc
    _ = ∑ i, ∑ j, ((if i < j then f i j else 0) + (if j < i then f j i else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact ht i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f:=fun i j => if j < i then f j i else 0)]

 

theorem tensorWedge_contraction (Q : ℕ) (s : Orbital Q × Orbital Q → ℂ)
    (hs : ∀ i j, s (j,i) = -s (i,j)) :
    wedgeAnnihilator Q 2
        (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ s) =
      (2:ℂ) • coefficientPairAnnihilator Q (fun i j => star (s (i,j))) := by
  rw [wedgeAnnihilator_mulVec]
  have hc (ij : Orbital Q × Orbital Q) := wedgeProductMatrix_contraction Q 1 1
    (oneParticleMatrix Q) (oneParticleMatrix Q) ij
  simp only [oneParticleMatrix_contraction] at hc
  simp only [hc, Fintype.sum_prod_type]
  have hh := symmetric_sum_upper (fun i j : Orbital Q => star (s (i,j)) •
    (annihilator Q j * annihilator Q i))
    (by
      intro i j
      have ha := eq_neg_of_add_eq_zero_left (annihilator_anticommute Q i j)
      rw [hs, star_neg, ha, neg_smul, smul_neg, neg_neg])
    (by intro i; simp only [annihilator_square, smul_zero])
  simpa only [coefficientPairAnnihilator, two_smul ℂ] using hh

 
theorem tensorWedge_intertwines (Q : ℕ) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) *
        wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) =
      wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
        tensorSum (spinGenerator Q s) (spinGenerator Q s) :=
  wedgeProductMatrix_intertwines Q 1 1 _ (spinGenerator_skew Q s) _ _ _ _
    (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s))
    (oneParticleMatrix_intertwines Q _ (spinGenerator_skew Q s))

 
def pairSpinMatrix (Q : ℕ) : Matrix (SectorOccupation Q 2) (Fin (2*Q-2+1)) ℂ :=
  fun S p => pairVector Q p.val S

 

theorem tensorWedge_pairSpinMatrix {Q : ℕ} (hQ : 1 ≤ Q) :
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *
      coupledSpinMatrix Q Q 1) =
      (Real.sqrt 2 : ℂ) •
        (pairSpinMatrix Q).submatrix id (Fin.cast (by omega)) := by
  ext S p
  have hv : wedgeAnnihilator Q 2
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) *ᵥ
        (fun ij => coupledSpinMatrix Q Q 1 ij p)) =
      wedgeAnnihilator Q 2 ((Real.sqrt 2 : ℂ) • pairVector Q p.val) := by
    rw [tensorWedge_contraction]
    · rw [wedgeAnnihilator_smul]
      simp only [pairVector, wedgeAnnihilator_annihilatorVector Q 2 _ (pairAnnihilator_mem Q _),
        Complex.star_def, Complex.conj_ofReal]
      unfold coupledSpinMatrix
      simp only [Complex.conj_ofReal]
      have he (i j : Orbital Q) :
          (coupledVector Q Q 1 p.val i.val j.val : ℂ) =
            (Real.sqrt 2 : ℂ)⁻¹ * (pairCoefficient Q p.val i j : ℂ) := by
        rw [pairCoefficient_eq_coupled hQ (by have := p.isLt; omega)]
        push_cast
        have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
        field_simp
      simp_rw [he]
      rw [coefficientPairAnnihilator_smul, smul_smul]
      congr 1
      have hs : (Real.sqrt 2 : ℂ)^2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
      have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
      field_simp
      linear_combination -hs
    · intro i j
      dsimp [coupledSpinMatrix]
      rw [coupledVector_antisymm hQ (by decide : Odd 1)]
      simp
  exact congrFun (wedgeAnnihilator_injective Q 2 hv) S

 
theorem pairSpinMatrix_intertwines {Q : ℕ} (hQ : 1 ≤ Q) (s : Fin 3) :
    sectorOneBody Q 2 (spinGenerator Q s) * pairSpinMatrix Q =
      pairSpinMatrix Q * spinGenerator (2*Q-2) s := by
  have h := coupledSpinMatrix_intertwines hQ hQ s
  have he : sectorOneBody Q 2 (spinGenerator Q s) *
      (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q 1) =
    (wedgeProductMatrix Q 1 1 (oneParticleMatrix Q) (oneParticleMatrix Q) * coupledSpinMatrix Q Q 1) *
      spinGenerator (Q+Q-2*1) s := by
    rw [← Matrix.mul_assoc, tensorWedge_intertwines, Matrix.mul_assoc, h, Matrix.mul_assoc]
  rw [tensorWedge_pairSpinMatrix hQ] at he
  have hdim : Q+Q-2*1 = 2*Q-2 := by omega
  simp only [Matrix.mul_smul, Matrix.smul_mul] at he
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (show Real.sqrt 2 ≠ 0 by positivity)
  have hf := smul_right_injective _ hn he
  have hc (n : ℕ) (e : n = 2*Q-2)
      (hc : sectorOneBody Q 2 (spinGenerator Q s) *
          (pairSpinMatrix Q).submatrix id (Fin.cast (congrArg (·+1) e)) =
        (pairSpinMatrix Q).submatrix id (Fin.cast (congrArg (·+1) e)) * spinGenerator n s) :
      sectorOneBody Q 2 (spinGenerator Q s) * pairSpinMatrix Q =
        pairSpinMatrix Q * spinGenerator (2*Q-2) s := by
    subst n
    simpa only [Fin.cast_refl, Matrix.submatrix_id_id] using hc
  exact hc _ hdim hf

end LaughlinFock
end

end OAI
