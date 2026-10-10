import Mathlib
import OAI.Analysis.LaughlinFock.Covariance

namespace OAI

/-! Flow. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix Matrix.Norms.Operator ComplexConjugate ComplexOrder
open NormedSpace

 
theorem matrixExp_conjugation_hasDerivAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A M : Matrix ι ι ℂ) (t : ℂ) :
    HasDerivAt (fun u : ℂ => exp (u • A) * M * exp (u • (-A)))
      (A * (exp (t • A) * M * exp (t • (-A))) -
        (exp (t • A) * M * exp (t • (-A))) * A) t := by
  have h := ((hasDerivAt_exp_smul_const' A t).mul_const M).mul
    (hasDerivAt_exp_smul_const (-A) t)
  convert! h using 1
  noncomm_ring

 

theorem matrixExp_conjugation_naturality {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ)
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (hL : ∀ M, L (X*M-M*X) = Y*L M-L M*Y)
    (M : Matrix ι ι ℂ) (t : ℂ) :
    L (exp (t • X) * M * exp (t • (-X))) =
      exp (t • Y) * L M * exp (t • (-Y)) := by
  let m (u : ℂ) := exp (u • X) * M * exp (u • (-X))
  let f (u : ℂ) := exp (u • (-Y)) * L (m u) * exp (u • Y)
  have hd (u : ℂ) : HasDerivAt f 0 u := by
    have hm : HasDerivAt (fun v => L (m v)) (Y*L (m u)-L (m u)*Y) u := by
      have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
        (matrixExp_conjugation_hasDerivAt X M u)
      change HasDerivAt (fun v => L (m v)) (L (X*m u-m u*X)) u at h
      rwa [hL] at h
    have h := ((hasDerivAt_exp_smul_const (-Y) u).mul hm).mul
      (hasDerivAt_exp_smul_const' Y u)
    simp only [Pi.mul_apply] at h
    convert! h using 1
    noncomm_ring
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  have he' : exp (t • (-Y)) * L (m t) * exp (t • Y) = L M := by
    simpa only [f, m, zero_smul, exp_zero, Matrix.one_mul, Matrix.mul_one] using he
  have hi₁ : exp (t • Y) * exp (t • (-Y)) = 1 := by
    have h := (exp_add_of_commute (Commute.refl (t • Y)).neg_right).symm
    simpa only [← smul_neg, ← smul_add, add_neg_cancel, smul_zero, exp_zero] using! h
  calc
    L (m t) = 1 * L (m t) * 1 := by simp
    _ = (exp (t • Y) * exp (t • (-Y))) * L (m t) *
          (exp (t • Y) * exp (t • (-Y))) := by rw [hi₁]
    _ = exp (t • Y) * (exp (t • (-Y)) * L (m t) * exp (t • Y)) *
          exp (t • (-Y)) := by noncomm_ring
    _ = _ := by rw [he']

 

theorem exteriorLift_exp_conjugation (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) (t : ℂ) :
    exteriorLift Q k (exp (t • sectorOneBody Q k A) * M *
        exp (t • (-sectorOneBody Q k A))) =
      exp (t • oneBodyLift Q A) * exteriorLift Q k M *
        exp (t • (-oneBodyLift Q A)) :=
  matrixExp_conjugation_naturality _ _ (exteriorLiftLinear Q k)
    (fun M => (oneBody_exteriorLift_commutator Q k A M).symm) M t

 

private theorem matrixExp_smul_unitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℂ) (hB : Bᴴ = B) (t : ℝ) :
    exp (((t : ℂ) * Complex.I) • B) ∈ Matrix.unitaryGroup ι ℂ := by
  let X : Matrix ι ι ℂ := ((t : ℂ) * Complex.I) • B
  have hX : Xᴴ = -X := by
    dsimp only [X]
    rw [Matrix.conjTranspose_smul, hB]
    simp [star_mul, mul_comm]
  have hstar : (exp X)ᴴ = exp (-X) := by
    rw [← Matrix.exp_conjTranspose, hX]
  change (exp X) ∈ unitary (Matrix ι ι ℂ)
  rw [Unitary.mem_iff]
  change (exp X)ᴴ * exp X = 1 ∧ exp X * (exp X)ᴴ = 1
  rw [hstar]
  constructor
  · simpa only [neg_add_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl X).neg_left).symm
  · simpa only [add_neg_cancel, exp_zero] using!
      (exp_add_of_commute (Commute.refl X).neg_right).symm


theorem oneBodyLift_exp_unitary (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : A.IsHermitian) (t : ℝ) :
    exp ((t * Complex.I) • oneBodyLift Q A) ∈
      Matrix.unitaryGroup (Occupation Q) ℂ :=
  matrixExp_smul_unitary (oneBodyLift Q A) (oneBodyLift_hermitian Q A hA).eq t

 
theorem exteriorLift_unitary_conjugation (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : A.IsHermitian)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) (t : ℝ) :
    exteriorLift Q k (exp ((t * Complex.I) • sectorOneBody Q k A) * M *
        (exp ((t * Complex.I) • sectorOneBody Q k A))ᴴ) =
      exp ((t * Complex.I) • oneBodyLift Q A) * exteriorLift Q k M *
        (exp ((t * Complex.I) • oneBodyLift Q A))ᴴ := by
  have hf : (oneBodyLift Q A)ᴴ = oneBodyLift Q A :=
    (oneBodyLift_hermitian Q A hA).eq
  have hs : (sectorOneBody Q k A)ᴴ = sectorOneBody Q k A := by
    rw [sectorOneBody_adjoint, hA.eq]
  have hB {ι : Type} [Fintype ι] [DecidableEq ι]
      (B : Matrix ι ι ℂ) (hB : Bᴴ = B) :
      (exp (((t : ℂ) * Complex.I) • B))ᴴ =
        exp (((t : ℂ) * Complex.I) • (-B)) := by
    rw [← Matrix.exp_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_smul, hB]
    simp [star_mul, mul_comm]
  rw [hB _ hs, hB _ hf]
  exact exteriorLift_exp_conjugation Q k A M _

end LaughlinFock
end

end OAI
