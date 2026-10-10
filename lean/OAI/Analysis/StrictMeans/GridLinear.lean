import OAI.Analysis.StrictMeans.FiniteEuler

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

def polyCoefficients (R : Type*) [Semiring R] : Polynomial R ≃ₗ[R] (ℕ →₀ R) :=
  (Polynomial.toFinsuppIsoLinear R).trans (AddMonoidAlgebra.coeffLinearEquiv R)

def coefficients : Chain ≃ₗ[ℚ] (ℕ × ℕ →₀ ℚ) :=
  (((polyCoefficients (Polynomial ℚ)).restrictScalars ℚ).trans
    (Finsupp.mapRange.linearEquiv (polyCoefficients ℚ))).trans
    ((Finsupp.curryLinearEquiv ℚ).symm.trans
      (Finsupp.domLCongr (Equiv.prodComm ℕ ℕ)))

@[simp] lemma coefficients_apply (p : Chain) (i j : ℕ) : coefficients p (i,j) = coeff p i j := rfl

def chainSpace (S : Set (ℕ × ℕ)) : Submodule ℚ Chain :=
  (Finsupp.supported ℚ ℚ S).comap coefficients.toLinearMap

lemma mem_chainSpace (S : Set (ℕ × ℕ)) (p : Chain) :
    p ∈ chainSpace S ↔ ∀ i j, (i,j) ∉ S → coeff p i j = 0 := by
  simp only [chainSpace,Submodule.mem_comap,Finsupp.mem_supported]
  simp only [Set.subset_def,Finset.mem_coe,Finsupp.mem_support_iff]
  constructor
  · intro h i j hi
    by_contra hn
    exact hi (h (i,j) hn)
  · intro h v hv
    by_contra he
    exact hv (h v.1 v.2 he)

def chainSpaceEquiv (S : Set (ℕ × ℕ)) : chainSpace S ≃ₗ[ℚ] (S →₀ ℚ) :=
  (coefficients.ofSubmodule' (Finsupp.supported ℚ ℚ S)).trans
    (Finsupp.supportedEquivFinsupp S)

instance finite_chainSpace (S : Set (ℕ × ℕ)) [Finite S] : FiniteDimensional ℚ (chainSpace S) :=
  (chainSpaceEquiv S).symm.finiteDimensional

lemma finrank_chainSpace (S : Set (ℕ × ℕ)) (hS : S.Finite) :
    finrank ℚ (chainSpace S) = S.ncard := by
  let := hS.fintype
  rw [(chainSpaceEquiv S).finrank_eq]
  simp

def horizontalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2) ∈ S}
def verticalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1,v.2+1) ∈ S}
def diagonalSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2+1) ∈ S}
def lowerSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1+1,v.2) ∈ S ∧ (v.1+1,v.2+1) ∈ S}
def upperSet (S : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := {v | v ∈ S ∧ (v.1,v.2+1) ∈ S ∧ (v.1+1,v.2+1) ∈ S}

abbrev EdgeSpace (S : Set (ℕ × ℕ)) := chainSpace (horizontalSet S) × chainSpace (verticalSet S) × chainSpace (diagonalSet S)
abbrev FaceSpace (S : Set (ℕ × ℕ)) := chainSpace (lowerSet S) × chainSpace (upperSet S)

def fullBoundary₁ : (Chain × Chain × Chain) →ₗ[ℚ] Chain where
  toFun p := boundary₁ p.1 p.2.1 p.2.2
  map_add' := by intros; simp only [boundary₁,Prod.fst_add,Prod.snd_add]; ring
  map_smul' := by
    intro r p
    change (x-1)*(r • p.1)+(y-1)*(r • p.2.1)+(x*y-1)*(r • p.2.2) = r • _
    simp only [mul_smul_comm,boundary₁,smul_add]

def fullBoundary₂ : (Chain × Chain) →ₗ[ℚ] (Chain × Chain × Chain) where
  toFun p := (faceH p.1 p.2,faceV p.1 p.2,faceD p.1 p.2)
  map_add' := by intros; ext <;> simp [faceH,faceV,faceD,mul_add] <;> ring
  map_smul' := by intros; ext <;> simp [faceH,faceV,faceD] <;> ring

end
end StrictInverseFirstPower.Grid

end

end OAI
