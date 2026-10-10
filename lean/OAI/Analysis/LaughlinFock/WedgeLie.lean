import Mathlib
import OAI.Analysis.LaughlinFock.CopyVectors
import OAI.Analysis.LaughlinFock.FockRotations

namespace OAI

/-! Wedge Lie. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem wedgeAnnihilator_neg (Q k : ℕ) (v : SectorOccupation Q k → ℂ) :
    wedgeAnnihilator Q k (-v) = -wedgeAnnihilator Q k v := by
  simp only [wedgeAnnihilator, Pi.neg_apply, star_neg, neg_smul, Finset.sum_neg_distrib]

 

theorem oneBody_wedgeAnnihilator_commutator_skew (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (v : SectorOccupation Q k → ℂ) :
    oneBodyLift Q A * wedgeAnnihilator Q k v -
      wedgeAnnihilator Q k v * oneBodyLift Q A =
      wedgeAnnihilator Q k (sectorOneBody Q k A *ᵥ v) := by
  rw [oneBody_wedgeAnnihilator_commutator, sectorOneBody_adjoint, hA]
  have hn := (sectorOneBodyLinear Q k).map_neg A
  change sectorOneBody Q k (-A) = -sectorOneBody Q k A at hn
  rw [hn, Matrix.neg_mulVec, wedgeAnnihilator_neg, neg_neg]

 

theorem sector_intertwiner_of_commutators {ι : Type*} [Fintype ι] (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (C : Matrix (SectorOccupation Q k) ι ℂ)
    (B : ι → FockMatrix Q)
    (hB : ∀ i, wedgeAnnihilator Q k (fun T => C T i) = B i)
    (hcomm : ∀ j, oneBodyLift Q A * B j - B j * oneBodyLift Q A =
      ∑ i, star (X i j) • B i) :
    sectorOneBody Q k A * C = C*X := by
  ext T j
  have he : wedgeAnnihilator Q k (sectorOneBody Q k A *ᵥ (fun T => C T j)) =
      wedgeAnnihilator Q k (C *ᵥ (fun i => X i j)) := by
    rw [← oneBody_wedgeAnnihilator_commutator_skew Q k A hA, hB,
      wedgeAnnihilator_mulVec]
    simp only [hB]
    exact hcomm j
  exact congrFun (wedgeAnnihilator_injective Q k he) T

 
theorem wedge_intertwiner_commutator {ι : Type*} [Fintype ι] (Q k : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (C : Matrix (SectorOccupation Q k) ι ℂ)
    (hC : sectorOneBody Q k A * C = C*X) (j : ι) :
    oneBodyLift Q A * wedgeAnnihilator Q k (fun T => C T j) -
      wedgeAnnihilator Q k (fun T => C T j) * oneBodyLift Q A =
      ∑ i, star (X i j) • wedgeAnnihilator Q k (fun T => C T i) := by
  rw [oneBody_wedgeAnnihilator_commutator_skew Q k A hA]
  have hh : sectorOneBody Q k A *ᵥ (fun T => C T j) = C *ᵥ (fun i => X i j) := by
    exact congrArg (fun M => fun T => M T j) hC
  rw [hh, wedgeAnnihilator_mulVec]

 
def tensorSum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) : Matrix (ι × κ) (ι × κ) ℂ :=
  Matrix.kronecker X 1 + Matrix.kronecker 1 Y

theorem tensorSum_apply {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ) (i j : ι × κ) :
    tensorSum X Y i j = (if i.2=j.2 then X i.1 j.1 else 0) +
      (if i.1=j.1 then Y i.2 j.2 else 0) := by
  rcases i with ⟨i₁,i₂⟩
  rcases j with ⟨j₁,j₂⟩
  simp only [tensorSum, Matrix.add_apply, Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul]

 

def wedgeProductMatrix {ι κ : Type*} (Q k l : ℕ)
    (V : Matrix (SectorOccupation Q k) ι ℂ) (W : Matrix (SectorOccupation Q l) κ ℂ) :
    Matrix (SectorOccupation Q (k+l)) (ι × κ) ℂ := fun S ij =>
  annihilatorVector Q (k+l)
    (wedgeAnnihilator Q l (fun T => W T ij.2) *
      wedgeAnnihilator Q k (fun T => V T ij.1)) S

theorem wedgeProductMatrix_contraction {ι κ : Type*} (Q k l : ℕ)
    (V : Matrix (SectorOccupation Q k) ι ℂ) (W : Matrix (SectorOccupation Q l) κ ℂ)
    (ij : ι × κ) :
    wedgeAnnihilator Q (k+l) (fun T => wedgeProductMatrix Q k l V W T ij) =
      wedgeAnnihilator Q l (fun T => W T ij.2) *
        wedgeAnnihilator Q k (fun T => V T ij.1) := by
  apply wedgeAnnihilator_annihilatorVector
  exact annihilationSpace_mul Q k l (wedgeAnnihilator_mem Q k _) (wedgeAnnihilator_mem Q l _)

 

theorem wedgeProductMatrix_intertwines {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (Q k l : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A)
    (X : Matrix ι ι ℂ) (Y : Matrix κ κ ℂ)
    (V : Matrix (SectorOccupation Q k) ι ℂ) (W : Matrix (SectorOccupation Q l) κ ℂ)
    (hV : sectorOneBody Q k A * V = V*X) (hW : sectorOneBody Q l A * W = W*Y) :
    sectorOneBody Q (k+l) A * wedgeProductMatrix Q k l V W =
      wedgeProductMatrix Q k l V W * tensorSum X Y := by
  apply sector_intertwiner_of_commutators Q (k+l) A hA (tensorSum X Y)
    (wedgeProductMatrix Q k l V W)
    (fun ij => wedgeAnnihilator Q l (fun T => W T ij.2) *
      wedgeAnnihilator Q k (fun T => V T ij.1))
    (wedgeProductMatrix_contraction Q k l V W)
  intro ij
  rw [matrix_commutator_mul, wedge_intertwiner_commutator Q l A hA Y W hW,
    wedge_intertwiner_commutator Q k A hA X V hV]
  simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    tensorSum_apply, star_add, apply_ite star, star_zero, add_smul, Finset.sum_add_distrib,
    Fintype.sum_prod_type, ite_smul, zero_smul]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact add_comm _ _

 
def oneParticleMatrix (Q : ℕ) : Matrix (SectorOccupation Q 1) (Orbital Q) ℂ := fun S i =>
  if S.val={i} then 1 else 0

theorem oneParticleMatrix_contraction (Q : ℕ) (i : Orbital Q) :
    wedgeAnnihilator Q 1 (fun S => oneParticleMatrix Q S i) = annihilator Q i := by
  have he : (fun S => oneParticleMatrix Q S i) = annihilatorVector Q 1 (annihilator Q i) := by
    funext S
    simp [oneParticleMatrix, annihilatorVector, annihilator_vacuum, eq_comm]
  rw [he, wedgeAnnihilator_annihilatorVector Q 1 _ (annihilator_mem Q i)]

 
theorem oneParticleMatrix_intertwines (Q : ℕ)
    (A : Matrix (Orbital Q) (Orbital Q) ℂ) (hA : Aᴴ = -A) :
    sectorOneBody Q 1 A * oneParticleMatrix Q = oneParticleMatrix Q * A := by
  apply sector_intertwiner_of_commutators Q 1 A hA A (oneParticleMatrix Q)
    (annihilator Q) (oneParticleMatrix_contraction Q)
  intro j
  rw [← neg_sub, annihilator_oneBody_commutator]
  have hh (i : Orbital Q) : star (A i j) = -A j i := by
    exact congrArg (fun M => M j i) hA
  simp only [hh, neg_smul, Finset.sum_neg_distrib]

end LaughlinFock
end

end OAI
