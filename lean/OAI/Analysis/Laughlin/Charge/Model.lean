import OAI.Analysis.Laughlin.Fock.LaughlinGap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

abbrev Hilbert (Q : ℕ) := EuclideanSpace ℂ (Finset (Fin (Q+1)))

def particleSector (Q n : ℕ) : Submodule ℂ (Hilbert Q) where
  carrier := {x | ∀ A, A.card ≠ n → x A = 0}
  zero_mem' := by intro A hA; rfl
  add_mem' := by intro x y hx hy A hA; simp [hx A hA,hy A hA]
  smul_mem' := by intro c x hx A hA; simp [hx A hA]

noncomputable def energy (Q : ℕ) (x : Hilbert Q) : ℝ :=
  sourceFockEnergy Q ((occupationEuclidean Q).symm x)

def unitSector (Q n : ℕ) : Set (Hilbert Q) :=
  {x | x ∈ particleSector Q n ∧ ‖x‖^2 = 1}

noncomputable def groundEnergy (Q n : ℕ) : ℝ := sInf (energy Q '' unitSector Q n)

noncomputable def groundKernel (Q n : ℕ) : Submodule ℂ (Hilbert Q) :=
  particleSector Q n ⊓ LinearMap.ker (euclideanFockHamiltonian Q)

noncomputable def neutralGap (Q n : ℕ) : ℝ :=
  sInf (energy Q '' {x | x ∈ unitSector Q n ∧ x ∈ (groundKernel Q n)ᗮ})

noncomputable def chargeGap (Q n : ℕ) : ℝ :=
  groundEnergy Q (n+1) + groundEnergy Q (n-1) - 2*groundEnergy Q n

noncomputable def annihilator (Q : ℕ) (i : Fin (Q+1)) : Hilbert Q →ₗ[ℂ] Hilbert Q :=
  (occupationEuclidean Q).toLinearMap.comp
    ((annihilate i).comp (occupationEuclidean Q).symm.toLinearMap)

noncomputable def groundOverlap (Q n : ℕ) (x : Hilbert Q) : ℝ :=
  ∑ i : Fin (Q+1), ‖(groundKernel Q n).starProjection (annihilator Q i x)‖^2

theorem energy_nonneg (Q : ℕ) (x : Hilbert Q) : 0 ≤ energy Q x := by
  unfold energy sourceFockEnergy
  exact Finset.sum_nonneg (fun p hp => occupationNormSq_nonneg Q _)

theorem groundEnergy_nonneg (Q n : ℕ) : 0 ≤ groundEnergy Q n := by
  apply Real.sInf_nonneg
  rintro t ⟨x,hx,rfl⟩
  exact energy_nonneg Q x

theorem neutralGap_nonneg (Q n : ℕ) : 0 ≤ neutralGap Q n := by
  apply Real.sInf_nonneg
  rintro t ⟨x,hx,rfl⟩
  exact energy_nonneg Q x

theorem unitSector_nonempty (Q n : ℕ) (hn : n ≤ Q+1) : (unitSector Q n).Nonempty := by
  obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq
    (show n ≤ (Finset.univ : Finset (Fin (Q+1))).card by simpa using hn)
  refine ⟨occupationEuclidean Q (occupationBasis Q A),?_,?_⟩
  · intro B hB
    change (occupationBasis Q).repr (occupationBasis Q A) B = 0
    have hne : A ≠ B := by intro he; subst B; exact hB hcard
    simp [Module.Basis.repr_self,hne]
  · rw [occupationEuclidean_norm]
    simp only [occupationNormSq,Module.Basis.repr_self,Finsupp.single_apply]
    rw [Finset.sum_eq_single A]
    · simp
    · intro B _ hBA
      simp [Ne.symm hBA]
    · simp

theorem groundEnergy_le (Q n : ℕ) (x : Hilbert Q) (hx : x ∈ unitSector Q n) :
    groundEnergy Q n ≤ energy Q x := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro t ⟨v,hv,rfl⟩
    exact energy_nonneg Q v
  · exact ⟨x,hx,rfl⟩

theorem groundEnergy_eq_zero_of_zero_mode (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ unitSector Q n) (hE : energy Q x = 0) : groundEnergy Q n = 0 := by
  exact le_antisymm (hE ▸ groundEnergy_le Q n x hx) (groundEnergy_nonneg Q n)

end Laughlin.Charge

end OAI
