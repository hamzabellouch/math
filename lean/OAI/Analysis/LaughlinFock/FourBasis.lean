import Mathlib
import OAI.Analysis.LaughlinFock.BesselComparison
import OAI.Analysis.LaughlinFock.ThreeSpectrum

namespace OAI

/-! Four Basis. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

 

theorem wedgeCoupledCoefficient_resolution (Q : ℕ) (ij kl : IncreasingPair Q) :
    (∑ r : CopyLabel Q, ∑ k : Fin (2*Q-2*r.val.val+1),
      wedgeCoupledCoefficient Q r.val.val k.val ij *
        wedgeCoupledCoefficient Q r.val.val k.val kl) = if ij=kl then 1 else 0 := by
  classical
  have h₁ := coupledVector_resolution Q Q ij.val kl.val
  have h₂ := coupledVector_resolution Q Q (ij.val.2,ij.val.1) kl.val
  have hn : (ij.val.2,ij.val.1) ≠ kl.val := by
    intro h
    have ha := congrArg Prod.fst h
    have hb := congrArg Prod.snd h
    have hi := ij.property
    have hk := kl.property
    dsimp only [Prod.fst, Prod.snd] at ha hb
    rw [← ha, ← hb] at hk
    exact lt_asymm hi hk
  rw [ite_eq_right hn] at h₂
  have hv := congrArg₂ (fun x y : ℝ => x-y) h₁ h₂
  rw [← Finset.sum_sub_distrib] at hv
  have ht (c : CoupledIndex Q Q) :
      coupledVector Q Q c.1.val c.2.val ij.val.1.val ij.val.2.val *
          coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val -
        coupledVector Q Q c.1.val c.2.val ij.val.2.val ij.val.1.val *
          coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val =
      if Odd c.1.val then wedgeCoupledCoefficient Q c.1.val c.2.val ij *
          wedgeCoupledCoefficient Q c.1.val c.2.val kl else 0 := by
    rw [coupledVector_swap (coupledIndex_bounds c).1 c.2.val ij.val.1.val ij.val.2.val]
    by_cases ho : Odd c.1.val
    · rw [ite_eq_left ho, ho.neg_one_pow]
      unfold wedgeCoupledCoefficient
      have hs := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
      linear_combination -(coupledVector Q Q c.1.val c.2.val ij.val.1.val ij.val.2.val *
        coupledVector Q Q c.1.val c.2.val kl.val.1.val kl.val.2.val) * hs
    · rw [ite_eq_right ho, (Nat.not_odd_iff_even.mp ho).neg_one_pow]
      ring
  simp only [ht, sub_zero, Subtype.val_inj] at hv
  rw [Fintype.sum_sigma] at hv
  rw [Nat.min_self, ← two_mul Q] at hv
  have he : (∑ r : CopyLabel Q, ∑ k : Fin (2*Q-2*r.val.val+1),
      wedgeCoupledCoefficient Q r.val.val k.val ij *
        wedgeCoupledCoefficient Q r.val.val k.val kl) =
      ∑ r : Fin (Q+1), if Odd r.val then ∑ k : Fin (2*Q-2*r.val+1),
        wedgeCoupledCoefficient Q r.val k.val ij *
          wedgeCoupledCoefficient Q r.val k.val kl else 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin (Q+1) => Odd r.val))
      (by intro r; simp) (fun r : Fin (Q+1) => ∑ k : Fin (2*Q-2*r.val+1),
        wedgeCoupledCoefficient Q r.val k.val ij * wedgeCoupledCoefficient Q r.val k.val kl)]
    rw [Finset.sum_filter]
  rw [he]
  simpa only [Nat.min_self, Finset.sum_ite_irrel, Finset.sum_const_zero, two_mul] using hv

 
def fullCouplingMatrix (n m : ℕ) :
    Matrix (Fin (n+1) × Fin (m+1)) (CoupledIndex n m) ℂ :=
  fun b c => coupledVector n m c.1.val c.2.val b.1.val b.2.val

theorem fullCouplingMatrix_complete (n m : ℕ) :
    fullCouplingMatrix n m * (fullCouplingMatrix n m)ᴴ = 1 := by
  classical
  ext b c
  have h := congrArg (fun x : ℝ => (x : ℂ)) (coupledVector_resolution n m b c)
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, fullCouplingMatrix,
    Complex.star_def, Complex.conj_ofReal, Matrix.one_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero] using h

 
def oddPairColumns (Q r : ℕ) :
    Matrix (IncreasingPair Q) (Fin (2*Q-2*r+1)) ℂ :=
  fun b k => wedgeCoupledCoefficient Q r k.val b

 
theorem oddPairColumns_complete (Q : ℕ) :
    (∑ r : CopyLabel Q, oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ) = 1 := by
  classical
  ext ij kl
  have h := congrArg (fun x : ℝ => (x : ℂ)) (wedgeCoupledCoefficient_resolution Q ij kl)
  simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, oddPairColumns,
    Complex.star_def, Complex.conj_ofReal, Matrix.one_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one,
    Complex.ofReal_zero] using h

 
def fourFactorEmbedding (Q r : ℕ) :
    Matrix (FourUncoupled Q) (Fin (2*Q-2+1) × Fin (2*Q-2*r+1)) ℂ :=
  Matrix.kronecker 1 (oddPairColumns Q r)

 
def composedCouplingMatrix (Q r : ℕ) :
    Matrix (FourUncoupled Q) (CoupledIndex (2*Q-2) (2*Q-2*r)) ℂ :=
  fun b c => composedCoupledVector Q r c.1.val c.2.val b

theorem composedCouplingMatrix_eq_product (Q r : ℕ) :
    composedCouplingMatrix Q r =
      fourFactorEmbedding Q r * fullCouplingMatrix (2*Q-2) (2*Q-2*r) := by
  classical
  ext b c
  simp only [Matrix.mul_apply, fourFactorEmbedding, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, one_mul, zero_mul, Fintype.sum_prod_type, fullCouplingMatrix]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    composedCouplingMatrix, composedCoupledVector, Complex.ofReal_sum, Complex.ofReal_mul,
    oddPairColumns]
  apply Finset.sum_congr rfl
  intro k _
  ring

 

theorem composedCouplingMatrix_complete (Q : ℕ) :
    (∑ r : CopyLabel Q, composedCouplingMatrix Q r.val.val *
      (composedCouplingMatrix Q r.val.val)ᴴ) = 1 := by
  simp_rw [composedCouplingMatrix_eq_product, Matrix.conjTranspose_mul]
  conv_lhs => arg 2; ext r; rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (fullCouplingMatrix _ _), fullCouplingMatrix_complete, Matrix.one_mul]
  simp only [fourFactorEmbedding, Matrix.kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  have hs : (∑ r : CopyLabel Q, Matrix.kronecker 1
      (oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ)) =
      Matrix.kronecker (1 : Matrix (Fin (2*Q-2+1)) (Fin (2*Q-2+1)) ℂ)
        (∑ r : CopyLabel Q, oddPairColumns Q r.val.val * (oddPairColumns Q r.val.val)ᴴ) := by
    ext b c
    simp only [Matrix.sum_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, Finset.mul_sum]
  simp only [Matrix.kronecker] at hs
  rw [hs, oddPairColumns_complete]
  exact Matrix.one_kronecker_one

end LaughlinFock
end

end OAI
