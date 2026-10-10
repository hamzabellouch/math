import Mathlib
import OAI.Analysis.Commutator.BicommutantOrbit
import OAI.Analysis.Commutator.StageDensity

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def operatorStage (n : ℕ) : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) :=
  (τ.gnsStarAlgHom.comp (φ n)).range

def stageAlgebra : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) :=
  ⨆ n, operatorStage τ I φ n

variable (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)

variable (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)

include e he in
lemma operatorStage_mono : Monotone (operatorStage τ I φ) := by
  intro n m hnm x hx
  obtain ⟨a, rfl⟩ := hx
  refine ⟨e hnm a, ?_⟩
  change τ.gnsStarAlgHom (φ m (e hnm a)) = τ.gnsStarAlgHom (φ n a)
  rw [he]

include e he in
lemma orbit_stageAlgebra :
    (orbitSubmodule (stageAlgebra τ I φ) (vacuum τ) : Set τ.GNS) =
      ⋃ n, stageSet τ I φ n := by
  have hS : (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)) =
      ⋃ n, (operatorStage τ I φ n : Set (τ.GNS →L[ℂ] τ.GNS)) :=
    StarSubalgebra.coe_iSup_of_directed (operatorStage_mono τ I φ e he).directed_le
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change a ∈ (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)) at ha
    rw [hS] at ha
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
    obtain ⟨b, rfl⟩ := hn
    refine Set.mem_iUnion.mpr ⟨n, b, ?_⟩
    exact (left_vacuum τ (φ n b)).symm
  · intro hx
    obtain ⟨n, b, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨τ.gnsStarAlgHom (φ n b), ?_, left_vacuum τ (φ n b)⟩
    change τ.gnsStarAlgHom (φ n b) ∈ (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS))
    rw [hS]
    exact Set.mem_iUnion.mpr ⟨n, b, rfl⟩

include e he in
theorem dense_stages_of_bicommutant_generation
    (hgen : ∀ a : A, τ.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer
        (stageAlgebra τ I φ : Set (τ.GNS →L[ℂ] τ.GNS)))) :
    Dense (⋃ n, stageSet τ I φ n) := by
  have hbase (a : A) : algebraVector τ a ∈ closure (⋃ n, stageSet τ I φ n) := by
    have h := bicommutant_mem_cyclicSubspace (stageAlgebra τ I φ) (hgen a) (vacuum τ)
    rw [left_vacuum] at h
    change algebraVector τ a ∈ closure (orbitSubmodule (stageAlgebra τ I φ) (vacuum τ) : Set τ.GNS) at h
    rwa [orbit_stageAlgebra τ I φ e he] at h
  intro x
  exact (algebraVector_dense τ).induction (fun _ ⟨a, ha⟩ => ha ▸ hbase a) isClosed_closure x

end Kadison.TracialGNS
end

end OAI
