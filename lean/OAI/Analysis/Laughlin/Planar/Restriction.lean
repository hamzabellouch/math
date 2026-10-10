import OAI.Analysis.Laughlin.Planar.DegreeRestriction
import OAI.Analysis.Laughlin.Fock.SharpGap
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

namespace Laughlin.Planar
open Fock Filter
open scoped BigOperators Topology Matrix

theorem pairMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    pairMatrix L c = LinearMap.toMatrix (occupationBasis L) (occupationBasis L) (pairEnd L c) := by
  ext A B
  simp only [pairMatrix,LinearMap.toMatrix_apply,pairEnd,LinearMap.sum_apply,
    LinearMap.smul_apply,Module.End.mul_apply,map_sum,Finsupp.finsetSum_apply,
    map_smul,Finsupp.smul_apply,smul_eq_mul]

theorem occupationInner_basis_left (L : ℕ) (A : Occupations L) (x : Space L) :
    occupationInner L (occupationBasis L A) x = (occupationBasis L).repr x A := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem occupationInner_basis_right (L : ℕ) (A : Occupations L) (x : Space L) :
    occupationInner L x (occupationBasis L A) = star ((occupationBasis L).repr x A) := by
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem pairCreateMatrix_toMatrix (L : ℕ) (c : Fin (L+1) → Fin (L+1) → ℂ) :
    (pairMatrix L c)ᴴ =
      LinearMap.toMatrix (occupationBasis L) (occupationBasis L) (pairCreateEnd L c) := by
  rw [pairMatrix_toMatrix]
  ext A B
  simp only [Matrix.conjTranspose_apply,LinearMap.toMatrix_apply]
  have h := pairCreate_pair_adjoint L c (occupationBasis L B) (occupationBasis L A)
  rw [occupationInner_basis_left,occupationInner_basis_right] at h
  simpa only [star_star] using (congrArg star h).symm

theorem sphereHamiltonian_toMatrix (L Q : ℕ) :
    sphereHamiltonian L Q = LinearMap.toMatrix (occupationBasis L) (occupationBasis L)
      (restrictedSphereHamiltonian L Q) := by
  unfold sphereHamiltonian restrictedSphereHamiltonian
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [LinearMap.toMatrix_mul]
  change (pairMatrix L _)ᴴ * pairMatrix L _ = _
  rw [pairCreateMatrix_toMatrix,pairMatrix_toMatrix]
  rfl

theorem sphere_pairEnergy_eq (L Q : ℕ) (x : Space L) :
    pairEnergy L (spherePairMatrix L Q) (fun A => (occupationBasis L).repr x A) =
      restrictedSphereEnergy L Q x := by
  unfold pairEnergy restrictedSphereEnergy
  apply Finset.sum_congr rfl
  intro p hp
  change (∑ A, ‖(pairMatrix L _ *ᵥ fun B => (occupationBasis L).repr x B) A‖^2) = _
  rw [pairMatrix_toMatrix,LinearMap.toMatrix_mulVec_repr]
  rfl

theorem sphere_squareNorm_eq (L Q : ℕ) (x : Space L) :
    squareNorm L (sphereHamiltonian L Q) (fun A => (occupationBasis L).repr x A) =
      occupationNormSq L (restrictedSphereHamiltonian L Q x) := by
  rw [squareNorm,sphereHamiltonian_toMatrix,LinearMap.toMatrix_mulVec_repr]
  rfl

theorem finite_degree_endpoint_of_fock_square (γstar : ℝ) (hγstar : 0 < γstar)
    (hSphere : ∀ γ : ℝ, 0 < γ → γ < γstar → ∀ᶠ Q : ℕ in atTop,
      ∀ x : Space Q, γ * sourceFockEnergy Q x ≤ occupationNormSq Q (sourceFockHamiltonian Q x))
    (L : ℕ) (x : Space L) (hx : DegreeAtMost L L x) :
    γstar * pairEnergy L (planarPairMatrix L) (fun A => (occupationBasis L).repr x A) ≤
      squareNorm L (planarHamiltonian L) (fun A => (occupationBasis L).repr x A) := by
  apply endpoint_of_sphere_blocks L γstar hγstar
  intro γ hγ hγstar'
  filter_upwards [hSphere γ hγ hγstar',eventually_ge_atTop (L+2)] with Q hs hQ
  have h := hs (fockInclusion L Q (by omega) x)
  rw [sourceFockEnergy_fockInclusion L Q hQ x hx,
    sourceFockHamiltonian_fockInclusion L Q hQ x hx,fockInclusion_normSq] at h
  simpa only [sphere_pairEnergy_eq,sphere_squareNorm_eq] using h

theorem finite_degree_endpoint (L : ℕ) (x : Space L) (hx : DegreeAtMost L L x) :
    gammaStar * pairEnergy L (planarPairMatrix L) (fun A => (occupationBasis L).repr x A) ≤
      squareNorm L (planarHamiltonian L) (fun A => (occupationBasis L).repr x A) := by
  apply finite_degree_endpoint_of_fock_square gammaStar
    (lt_trans (by norm_num : (0 : ℝ) < 1/25) one_twenty_fifth_lt_gammaStar)
    (fun γ _hγ hγstar => physical_fock_square_eventually_sharp γ hγstar) L x hx

end Laughlin.Planar

end OAI
