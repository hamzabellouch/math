import OAI.Analysis.Laughlin.Fock.SpinContinuity

namespace OAI

namespace Laughlin.Fock
open Rotation
open scoped BigOperators Matrix

noncomputable def fockSpinMatrix (Q : ℕ) (g : SourceSU2) :
    Matrix (Finset (Fin (Q+1))) (Finset (Fin (Q+1))) ℂ :=
  fun A B => (occupationBasis Q).repr (exteriorRotation Q g (occupationBasis Q B)) A

theorem fockSpinMatrix_mul (Q : ℕ) (g h : SourceSU2) :
    fockSpinMatrix Q (g*h) = fockSpinMatrix Q g*fockSpinMatrix Q h := by
  funext A B
  change (occupationBasis Q).repr (exteriorRotation Q (g*h) (occupationBasis Q B)) A = _
  rw [← exteriorRotation_mul]
  have hx := (occupationBasis Q).sum_repr (exteriorRotation Q h (occupationBasis Q B))
  conv_lhs => rw [← hx]
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    Matrix.mul_apply,fockSpinMatrix]
  apply Finset.sum_congr rfl
  intro C hC
  exact mul_comm _ _

theorem fockSpinMatrix_one (Q : ℕ) : fockSpinMatrix Q 1 = 1 := by
  funext A B
  simp [fockSpinMatrix,exteriorRotation_one,Module.Basis.repr_self,Finsupp.single_apply,Matrix.one_apply,eq_comm]

noncomputable def fockSpinRepresentation (Q : ℕ) :
    SourceSU2 →* Matrix (Finset (Fin (Q+1))) (Finset (Fin (Q+1))) ℂ where
  toFun := fockSpinMatrix Q
  map_one' := fockSpinMatrix_one Q
  map_mul' := fockSpinMatrix_mul Q

theorem occupationInner_basis (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    occupationInner Q (occupationBasis Q A) (occupationBasis Q B) = if A=B then 1 else 0 := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem fockSpinRepresentation_unitary (Q : ℕ) (g : SourceSU2) :
    fockSpinRepresentation Q g ∈ Matrix.unitaryGroup (Finset (Fin (Q+1))) ℂ := by
  apply Matrix.mem_unitaryGroup_iff'.mpr
  rw [Matrix.star_eq_conjTranspose]
  funext A B
  have h := exteriorRotation_unitary Q g (occupationBasis Q A) (occupationBasis Q B)
  rw [occupationInner_basis] at h
  simpa only [occupationInner,fockSpinRepresentation,fockSpinMatrix,MonoidHom.coe_mk,OneHom.coe_mk,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.one_apply] using h

theorem fockSpinRepresentation_continuous (Q : ℕ) (A B : Finset (Fin (Q+1))) :
    Continuous (fun g => fockSpinRepresentation Q g A B) :=
  exteriorRotation_basis_continuous Q A B

theorem fockSpinRepresentation_coordinates (Q : ℕ) (g : SourceSU2) (x : Space Q) :
    (fun A => (occupationBasis Q).repr (exteriorRotation Q g x) A) =
      fockSpinRepresentation Q g *ᵥ (fun A => (occupationBasis Q).repr x A) := by
  have hx := (occupationBasis Q).sum_repr x
  conv_lhs => rw [← hx]
  funext A
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct,fockSpinRepresentation,fockSpinMatrix,MonoidHom.coe_mk,OneHom.coe_mk]
  apply Finset.sum_congr rfl
  intro B hB
  exact mul_comm _ _

end Laughlin.Fock

end OAI
