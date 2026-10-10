import OAI.Analysis.Laughlin.Charge.Model
import OAI.Analysis.Laughlin.Fock.Coordinates

namespace OAI

namespace Laughlin.Charge
open Fock
open scoped BigOperators InnerProductSpace

def FockDegree (Q : ℕ) (n : ℤ) (x : Space Q) : Prop :=
  ∀ A, (A.card : ℤ) ≠ n → (occupationBasis Q).repr x A = 0

theorem fockDegree_sum {Q : ℕ} {n : ℤ} {ι : Type*} (s : Finset ι)
    (x : ι → Space Q) (hx : ∀ i ∈ s, FockDegree Q n (x i)) :
    FockDegree Q n (∑ i ∈ s, x i) := by
  intro A hA
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero (fun i hi => hx i hi A hA)

theorem fockDegree_smul {Q : ℕ} {n : ℤ} {x : Space Q} (hx : FockDegree Q n x)
    (c : ℂ) : FockDegree Q n (c • x) := by
  intro A hA
  simp [hx A hA]

theorem fockDegree_annihilate {Q : ℕ} {n : ℤ} {x : Space Q}
    (hx : FockDegree Q n x) (i : Fin (Q+1)) :
    FockDegree Q (n-1) (annihilate i x) := by
  intro A hA
  rw [annihilate_coordinate]
  split_ifs with hi
  · rfl
  · rw [hx (insert i A) (by rw [Finset.card_insert_of_notMem hi]; omega),mul_zero]

theorem fockDegree_create {Q : ℕ} {n : ℤ} {x : Space Q}
    (hx : FockDegree Q n x) (i : Fin (Q+1)) :
    FockDegree Q (n+1) (create i x) := by
  intro A hA
  rw [create_coordinate]
  split_ifs with hi
  · rw [hx (A.erase i) (by rw [Finset.card_erase_of_mem hi]; have := Finset.card_pos.mpr ⟨i,hi⟩; omega),mul_zero]
  · rfl

theorem fockDegree_pair {Q : ℕ} {n : ℤ} {x : Space Q}
    (hx : FockDegree Q n x) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    FockDegree Q (n-2) (pairEnd Q c x) := by
  simp only [pairEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  apply fockDegree_sum
  intro i _
  apply fockDegree_sum
  intro j _
  apply fockDegree_smul
  simpa [sub_sub] using fockDegree_annihilate (fockDegree_annihilate hx i) j

theorem fockDegree_pairCreate {Q : ℕ} {n : ℤ} {x : Space Q}
    (hx : FockDegree Q n x) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    FockDegree Q (n+2) (pairCreateEnd Q c x) := by
  simp only [pairCreateEnd,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  apply fockDegree_sum
  intro i _
  apply fockDegree_sum
  intro j _
  apply fockDegree_smul
  simpa [add_assoc] using fockDegree_create (fockDegree_create hx j) i

theorem fockDegree_hamiltonian {Q : ℕ} {n : ℤ} {x : Space Q}
    (hx : FockDegree Q n x) : FockDegree Q n (sourceFockHamiltonian Q x) := by
  simp only [sourceFockHamiltonian,LinearMap.sum_apply,Module.End.mul_apply]
  apply fockDegree_sum
  intro p hp
  unfold sourcePairCreateEnd sourcePairEnd
  simpa only [sub_add_cancel] using fockDegree_pairCreate (fockDegree_pair hx _) _

theorem hamiltonian_mem_sector (Q n : ℕ) (x : Hilbert Q)
    (hx : x ∈ particleSector Q n) : euclideanFockHamiltonian Q x ∈ particleSector Q n := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  have hv : FockDegree Q n v := by
    intro A hA
    exact hx A (by exact_mod_cast hA)
  rw [euclideanFockHamiltonian_apply]
  intro A hA
  exact fockDegree_hamiltonian hv A (by exact_mod_cast hA)

noncomputable def sectorHamiltonian (Q n : ℕ) : Module.End ℂ (particleSector Q n) :=
  (euclideanFockHamiltonian Q).restrict (hamiltonian_mem_sector Q n)

theorem sectorHamiltonian_symmetric (Q n : ℕ) : LinearMap.IsSymmetric (𝕜 := ℂ) (E := particleSector Q n) (sectorHamiltonian Q n) :=
  (euclideanFockHamiltonian_symmetric Q).restrict_invariant (hamiltonian_mem_sector Q n)

theorem energy_eq_inner (Q : ℕ) (x : Hilbert Q) :
    energy Q x = (inner ℂ (euclideanFockHamiltonian Q x) x).re := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  rw [euclideanFockHamiltonian_apply,occupationEuclidean_inner,sourceFockHamiltonian_quadratic]
  simp [energy]

theorem energy_eq_zero_iff (Q : ℕ) (x : Hilbert Q) :
    energy Q x = 0 ↔ euclideanFockHamiltonian Q x = 0 := by
  obtain ⟨v,rfl⟩ := (occupationEuclidean Q).surjective x
  simp only [energy,LinearEquiv.symm_apply_apply,euclideanFockHamiltonian_apply]
  rw [← sourceFockHamiltonian_kernel]
  exact (map_eq_zero_iff (occupationEuclidean Q) (LinearEquiv.injective _)).symm

end Laughlin.Charge

end OAI
