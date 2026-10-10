import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardGlobal
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.StdBasis

namespace OAI

/-! Actual occupation-basis diagonal action for the global Hubbard model. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators
variable {Q : ℕ}

def fockBasis (Q : ℕ) : Module.Basis (Finset (Fin (Q + 1))) ℂ (Space Q) :=
  (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra

theorem annihilate_unoccupied_wedge (i : Fin (Q + 1)) (n : ℕ)
    (w : Fin n → Fin (Q + 1)) (hi : ∀ k, w k ≠ i) :
    annihilate i (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k))) = 0 := by
  induction n with
  | zero => simp [annihilate]
  | succ n ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode (w 0)) *
        ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0
    rw [CliffordAlgebra.contractLeft_ι_mul]
    have hmode : (LinearMap.proj i : Orbital Q →ₗ[ℂ] ℂ) (mode (w 0)) = 0 := by
      simp [LinearMap.proj, mode, Ne.symm (hi 0)]
    have htail := ih (fun k => w k.succ) (fun k => hi k.succ)
    change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ιMulti ℂ n (fun k => mode (w k.succ))) = 0 at htail
    rw [hmode, htail]
    simp

theorem annihilate_unoccupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∉ A) :
    annihilate i (fockBasis Q A) = 0 := by
  let S : Set.powersetCard (Fin (Q + 1)) A.card := ⟨A, rfl⟩
  have hn (k : Fin A.card) : Set.powersetCard.ofFinEmbEquiv.symm S k ≠ i := by
    intro h
    apply hi
    rw [← h]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S _).mp ⟨k, rfl⟩
  have h := annihilate_unoccupied_wedge i A.card
    (Set.powersetCard.ofFinEmbEquiv.symm S) hn
  change annihilate i ((Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val) = 0
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simpa only [ExteriorAlgebra.ιMulti_family, Function.comp_def, Pi.basisFun_apply, mode] using h

theorem fockBasis_singleton (i : Fin (Q + 1)) :
    fockBasis Q {i} = ExteriorAlgebra.ι ℂ (mode i) := by
  let S : Set.powersetCard (Fin (Q + 1)) 1 := ⟨{i}, Finset.card_singleton i⟩
  have hi : Set.powersetCard.ofFinEmbEquiv.symm S 0 = i := by
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S
      (Set.powersetCard.ofFinEmbEquiv.symm S 0)).mp ⟨0, rfl⟩
    exact Finset.mem_singleton.mp hm
  change (Pi.basisFun ℂ (Fin (Q + 1))).ExteriorAlgebra S.val = _
  rw [ExteriorAlgebra.basis_apply_powersetCard]
  simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one, Function.comp_apply, hi]
  simp [Pi.basisFun_apply, mode]

theorem create_occupied_basis (i : Fin (Q + 1))
    (A : Finset (Fin (Q + 1))) (hi : i ∈ A) : create i (fockBasis Q A) = 0 := by
  have hd : ¬Disjoint ({i} : Finset (Fin (Q + 1))) A := by simpa using hi
  have h := ExteriorAlgebra.basis_mul_of_not_disjoint (Pi.basisFun ℂ (Fin (Q + 1)))
    (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard (Fin (Q + 1)) 1)
    (⟨A, rfl⟩ : Set.powersetCard (Fin (Q + 1)) A.card) hd
  change fockBasis Q {i} * fockBasis Q A = 0 at h
  rw [fockBasis_singleton] at h
  exact h

/-- Each actual number operator is diagonal in the full occupation
basis, including every spectator mode. -/
theorem number_basis (i : Fin (Q + 1)) (A : Finset (Fin (Q + 1))) :
    number i (fockBasis Q A) = if i ∈ A then fockBasis Q A else 0 := by
  by_cases hi : i ∈ A
  · have h := LinearMap.congr_fun (mixed_car i i) (fockBasis Q A)
    change annihilate i (create i (fockBasis Q A)) +
      create i (annihilate i (fockBasis Q A)) =
        (if i = i then (1 : ℂ) else 0) • fockBasis Q A at h
    simpa [hi, create_occupied_basis i A hi, number, transfer] using h
  · simpa [hi, number, transfer] using
      congrArg (create i) (annihilate_unoccupied_basis i A hi)

end ContinuumCoulomb.HubbardGlobal

end

end OAI
