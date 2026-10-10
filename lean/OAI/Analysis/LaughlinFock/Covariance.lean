import Mathlib
import OAI.Analysis.LaughlinFock.ThreeGram

namespace OAI

/-! Covariance. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 

def oneBodyLift (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) : FockMatrix Q :=
  ∑ i, ∑ j, A i j • ((annihilator Q i)ᴴ * annihilator Q j)

theorem oneBodyLift_add (Q : ℕ) (A B : Matrix (Orbital Q) (Orbital Q) ℂ) :
    oneBodyLift Q (A+B) = oneBodyLift Q A + oneBodyLift Q B := by
  simp [oneBodyLift, add_smul, Finset.sum_add_distrib]

theorem oneBodyLift_smul (Q : ℕ) (c : ℂ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    oneBodyLift Q (c • A) = c • oneBodyLift Q A := by
  simp [oneBodyLift, smul_smul, Finset.smul_sum]

def oneBodyLiftLinear (Q : ℕ) :
    Matrix (Orbital Q) (Orbital Q) ℂ →ₗ[ℂ] FockMatrix Q where
  toFun := oneBodyLift Q
  map_add' := oneBodyLift_add Q
  map_smul' := oneBodyLift_smul Q

theorem oneBodyLift_adjoint (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    (oneBodyLift Q A)ᴴ = oneBodyLift Q Aᴴ := by
  simp only [oneBodyLift, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

theorem oneBodyLift_hermitian (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (hA : A.IsHermitian) : (oneBodyLift Q A).IsHermitian := by
  change (oneBodyLift Q A)ᴴ = _
  rw [oneBodyLift_adjoint, hA.eq]

 
theorem annihilator_oneBody_unit_commutator (Q : ℕ) (k i j : Orbital Q) :
    annihilator Q k * ((annihilator Q i)ᴴ * annihilator Q j) -
      ((annihilator Q i)ᴴ * annihilator Q j) * annihilator Q k =
        if k=i then annihilator Q j else 0 := by
  have h1 := congrArg (fun X : FockMatrix Q => X * annihilator Q j)
    (annihilator_adjoint_anticommute Q k i)
  have h2 := congrArg (fun X : FockMatrix Q => (annihilator Q i)ᴴ * X)
    (annihilator_anticommute Q k j)
  simp only [Matrix.add_mul, Matrix.mul_assoc, ite_mul, Matrix.one_mul,
    Matrix.zero_mul] at h1
  simp only [Matrix.mul_add, Matrix.mul_zero] at h2
  calc
    _ = annihilator Q k * ((annihilator Q i)ᴴ * annihilator Q j) +
          (annihilator Q i)ᴴ * (annihilator Q k * annihilator Q j) -
          ((annihilator Q i)ᴴ * (annihilator Q k * annihilator Q j) +
          (annihilator Q i)ᴴ * (annihilator Q j * annihilator Q k)) := by noncomm_ring
    _ = _ := by rw [h1, h2, sub_zero]

theorem annihilator_oneBody_commutator (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (k : Orbital Q) :
    annihilator Q k * oneBodyLift Q A - oneBodyLift Q A * annihilator Q k =
      ∑ j, A k j • annihilator Q j := by
  classical
  simp only [oneBodyLift, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub]
  simp_rw [annihilator_oneBody_unit_commutator, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

theorem oneBody_creator_commutator (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (k : Orbital Q) :
    oneBodyLift Q A * (annihilator Q k)ᴴ - (annihilator Q k)ᴴ * oneBodyLift Q A =
      ∑ i, A i k • (annihilator Q i)ᴴ := by
  have h := congrArg Matrix.conjTranspose (annihilator_oneBody_commutator Q Aᴴ k)
  simpa only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, oneBodyLift_adjoint,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_apply, star_star] using h

 
theorem matrix_commutator_mul {ι : Type*} [Fintype ι]
    (X Y Z : Matrix ι ι ℂ) :
    X * (Y*Z) - (Y*Z) * X =
      (X*Y-Y*X)*Z + Y*(X*Z-Z*X) := by noncomm_ring

 

theorem oneBody_annihilator_commutator_mem (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (j : Orbital Q) :
    oneBodyLift Q A * annihilator Q j - annihilator Q j * oneBodyLift Q A ∈
      AnnihilationSpace Q 1 := by
  rw [← neg_sub, annihilator_oneBody_commutator]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (annihilator_mem Q i)

theorem oneBody_annihilatorList_commutator_mem (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (js : List (Orbital Q)) :
    oneBodyLift Q A * annihilatorList Q js - annihilatorList Q js * oneBodyLift Q A ∈
      AnnihilationSpace Q js.length := by
  induction js with
  | nil => simp only [annihilatorList_nil, Matrix.mul_one, Matrix.one_mul, sub_self]; exact Submodule.zero_mem _
  | cons j js ih =>
    rw [annihilatorList_cons, matrix_commutator_mul]
    apply Submodule.add_mem
    · simpa only [List.length_cons, Nat.add_comm] using
        annihilationSpace_mul Q 1 js.length (annihilator_mem Q j) ih
    · simpa only [List.length_cons, Nat.add_comm] using
        annihilationSpace_mul Q 1 js.length
          (oneBody_annihilator_commutator_mem Q A j) (annihilatorList_mem Q js _ rfl)

theorem oneBody_annihilationSpace_commutator_mem (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q k) :
    oneBodyLift Q A * M - M * oneBodyLift Q A ∈ AnnihilationSpace Q k := by
  rw [annihilationSpace_normal_form Q k M hM]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    ← Finset.sum_sub_distrib, ← smul_sub]
  apply Submodule.sum_mem
  intro S _
  apply Submodule.smul_mem
  have h := oneBody_annihilatorList_commutator_mem Q A (S.val.sort (· ≤ ·))
  simpa only [Finset.length_sort, S.property, basisAnnihilator] using h

 
theorem oneBodyLift_vacuum_row (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (S : Occupation Q) : oneBodyLift Q A ∅ S = 0 := by
  simp only [oneBodyLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    ← creator_eq_adjoint, creator_mul_vacuum_zero, mul_zero, Finset.sum_const_zero]

 
theorem oneBodyLift_vacuum_column (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (S : Occupation Q) : oneBodyLift Q A S ∅ = 0 := by
  simp only [oneBodyLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    mul_annihilator_vacuum_zero, mul_zero, Finset.sum_const_zero]

 

theorem oneBodyLift_entry_eq_zero (Q : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (S T : Occupation Q) (h : S.card ≠ T.card) : oneBodyLift Q A S T = 0 := by
  classical
  simp only [oneBodyLift, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  suffices hh : ((annihilator Q i)ᴴ * annihilator Q j) S T = 0 by rw [hh, mul_zero]
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro R _
  rw [Matrix.conjTranspose_apply]
  by_cases hR : R.card+1=S.card
  · rw [annihilator_entry_eq_zero j R T (by omega), mul_zero]
  · rw [annihilator_entry_eq_zero i R S hR, star_zero, zero_mul]

 
def sectorOneBody (Q k : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ :=
  (oneBodyLift Q A).submatrix Subtype.val Subtype.val

theorem sectorOneBody_adjoint (Q k : ℕ) (A : Matrix (Orbital Q) (Orbital Q) ℂ) :
    (sectorOneBody Q k A)ᴴ = sectorOneBody Q k Aᴴ := by
  rw [sectorOneBody, Matrix.conjTranspose_submatrix, oneBodyLift_adjoint]
  rfl

 

theorem oneBody_basis_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (T : SectorOccupation Q k) :
    oneBodyLift Q A * basisAnnihilator Q T.val -
      basisAnnihilator Q T.val * oneBodyLift Q A =
      -∑ S, sectorOneBody Q k A T S • basisAnnihilator Q S.val := by
  classical
  apply annihilationSpace_ext Q k
    (oneBody_annihilationSpace_commutator_mem Q k A _ (basisAnnihilator_mem Q k T))
    (Submodule.neg_mem _ (Submodule.sum_mem _ fun S _ =>
      Submodule.smul_mem _ _ (basisAnnihilator_mem Q k S)))
  intro S
  simp only [Matrix.sub_apply, Matrix.mul_apply, oneBodyLift_vacuum_row,
    zero_mul, Finset.sum_const_zero, zero_sub, basisAnnihilator_vacuum,
    ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Subtype.val_inj, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  rfl

 
theorem oneBody_basisCreator_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (T : SectorOccupation Q k) :
    oneBodyLift Q A * (basisAnnihilator Q T.val)ᴴ -
      (basisAnnihilator Q T.val)ᴴ * oneBodyLift Q A =
      ∑ S, sectorOneBody Q k A S T • (basisAnnihilator Q S.val)ᴴ := by
  have h := congrArg Matrix.conjTranspose (oneBody_basis_commutator Q k Aᴴ T)
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, oneBodyLift_adjoint,
    Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_neg, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_smul] at h
  rw [← neg_sub, h, neg_neg]
  congr 1
  funext S
  congr 1
  rw [← sectorOneBody_adjoint, Matrix.conjTranspose_apply, star_star]

 

theorem oneBody_wedgeAnnihilator_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (v : SectorOccupation Q k → ℂ) :
    oneBodyLift Q A * wedgeAnnihilator Q k v -
      wedgeAnnihilator Q k v * oneBodyLift Q A =
      -wedgeAnnihilator Q k ((sectorOneBody Q k A)ᴴ *ᵥ v) := by
  classical
  simp only [wedgeAnnihilator, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, ← Finset.sum_sub_distrib, ← smul_sub,
    oneBody_basis_commutator, smul_neg, Finset.sum_neg_distrib, Matrix.mulVec,
    dotProduct, Matrix.conjTranspose_apply, star_sum, star_mul, star_star,
    Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

 

theorem oneBody_exteriorLift_commutator (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ)
    (M : Matrix (SectorOccupation Q k) (SectorOccupation Q k) ℂ) :
    oneBodyLift Q A * exteriorLift Q k M - exteriorLift Q k M * oneBodyLift Q A =
      exteriorLift Q k (sectorOneBody Q k A * M - M * sectorOneBody Q k A) := by
  classical
  let R := sectorOneBody Q k A
  let C (S T : SectorOccupation Q k) :=
    (basisAnnihilator Q S.val)ᴴ * basisAnnihilator Q T.val
  have hprod (S T : SectorOccupation Q k) :
      oneBodyLift Q A * C S T - C S T * oneBodyLift Q A =
        (∑ U, R U S • C U T) - ∑ U, R T U • C S U := by
    dsimp only [C]
    rw [matrix_commutator_mul, oneBody_basisCreator_commutator, oneBody_basis_commutator]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_neg,
      Matrix.mul_sum, Matrix.mul_smul, sub_eq_add_neg, R]
  have hleft : (∑ S, ∑ T, ∑ U, (M S T * R U S) • C U T) =
      exteriorLift Q k (R*M) := by
    unfold exteriorLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext T
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    apply Finset.sum_congr rfl
    intro T _
    apply Finset.sum_congr rfl
    intro S _
    rw [mul_comm]
  have hright : (∑ S, ∑ T, ∑ U, (M S T * R T U) • C S U) =
      exteriorLift Q k (M*R) := by
    unfold exteriorLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro S _
    exact Finset.sum_comm
  calc
    _ = ∑ S, ∑ T, M S T •
        (oneBodyLift Q A * C S T - C S T * oneBodyLift Q A) := by
      simp only [exteriorLift, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul, ← Finset.sum_sub_distrib, smul_sub, C]
    _ = exteriorLift Q k (R*M) - exteriorLift Q k (M*R) := by
      simp only [hprod, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
      rw [hleft, hright]
    _ = _ := ((exteriorLiftLinear Q k).map_sub (R*M) (M*R)).symm

 

theorem oneBodyLift_commutator (Q : ℕ) (A B : Matrix (Orbital Q) (Orbital Q) ℂ) :
    oneBodyLift Q A * oneBodyLift Q B - oneBodyLift Q B * oneBodyLift Q A =
      oneBodyLift Q (A*B-B*A) := by
  classical
  let C (i j : Orbital Q) := (annihilator Q i)ᴴ * annihilator Q j
  have hp (i j : Orbital Q) :
      oneBodyLift Q A * C i j - C i j * oneBodyLift Q A =
        (∑ r, A r i • C r j) - ∑ r, A j r • C i r := by
    dsimp only [C]
    rw [matrix_commutator_mul, oneBody_creator_commutator,
      ← neg_sub (annihilator Q j * oneBodyLift Q A) (oneBodyLift Q A * annihilator Q j),
      annihilator_oneBody_commutator]
    simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_neg,
      Matrix.mul_sum, Matrix.mul_smul, sub_eq_add_neg]
  have hl : (∑ i, ∑ j, ∑ r, (B i j * A r i) • C r j) = oneBodyLift Q (A*B) := by
    unfold oneBodyLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext j
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  have hr : (∑ i, ∑ j, ∑ r, (B i j * A j r) • C i r) = oneBodyLift Q (B*A) := by
    unfold oneBodyLift
    simp only [Matrix.mul_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  calc
    _ = ∑ i, ∑ j, B i j • (oneBodyLift Q A * C i j - C i j * oneBodyLift Q A) := by
      change oneBodyLift Q A * (∑ i, ∑ j, B i j • C i j) -
        (∑ i, ∑ j, B i j • C i j) * oneBodyLift Q A = _
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
        Matrix.smul_mul, ← Finset.sum_sub_distrib, smul_sub]
    _ = oneBodyLift Q (A*B) - oneBodyLift Q (B*A) := by
      simp only [hp, smul_sub, Finset.smul_sum, smul_smul, Finset.sum_sub_distrib]
      rw [hl, hr]
    _ = _ := ((oneBodyLiftLinear Q).map_sub (A*B) (B*A)).symm

end LaughlinFock
end

end OAI
