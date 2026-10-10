import Mathlib
import OAI.Analysis.Commutator.CycleInvariants3
import OAI.Analysis.Commutator.CyclePairTrace2

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

namespace Kadison.SchurWeyl

variable {J : Type*}

def IsEndpointPairing (σ : Equiv.Perm (Option J)) : Prop :=
  σ none = none ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = none

lemma some_removeNone_of_fixed (σ : Equiv.Perm (Option J)) (hσ : σ none = none) (j : J) :
    some (σ.removeNone j) = σ (some j) := by
  apply Equiv.removeNone_some
  cases he : σ (some j) with
  | none =>
    have hh := σ.injective (he.trans hσ.symm)
    cases hh
  | some k => exact ⟨k, rfl⟩

def pairingOfEndpointPerm (σ : Equiv.Perm (Option J)) (hσ : IsEndpointPairing σ) : Pairing J :=
  ⟨σ.removeNone, (by
    constructor
    · intro j
      apply Option.some_injective
      rw [some_removeNone_of_fixed σ hσ.1, some_removeNone_of_fixed σ hσ.1]
      exact hσ.2.1 (some j)
    · intro j hj
      have hh : σ (some j) = some j := by
        rw [← some_removeNone_of_fixed σ hσ.1, hj]
      exact Option.some_ne_none j (hσ.2.2 (some j) hh))⟩

def endpointPairingEquiv : Pairing J ≃ {σ : Equiv.Perm (Option J) // IsEndpointPairing σ} where
  toFun τ := ⟨endpointPairingPerm τ, (by
    refine ⟨rfl, ?_, ?_⟩
    · intro j
      cases j with
      | none => rfl
      | some j => simp only [endpointPairingPerm_some, Pairing.apply_apply]
    · intro j hj
      cases j with
      | none => rfl
      | some j =>
        have hh : τ j = j := Option.some.inj hj
        exact (τ.apply_ne j hh).elim)⟩
  invFun σ := pairingOfEndpointPerm σ.1 σ.2
  left_inv τ := by
    apply Subtype.ext
    exact Equiv.removeNone_optionCongr τ.val
  right_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro j
    cases j with
    | none => exact σ.2.1.symm
    | some j => exact some_removeNone_of_fixed σ.1 σ.2.1 j

variable [Fintype J] [LinearOrder J]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem centered_expansion_contractions (d : Equiv.Perm (Option J) → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card (Option J) + 1 → d σ = 0)
    (A : Option J → Matrix I I ℂ) (hA : ∀ j, Matrix.trace (A (some j)) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ((Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none)) *
        ∑ τ : Pairing J, d (endpointPairingPerm τ) *
          Pairing.contraction τ
            (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
            (fun j => A (some j)) := by
  classical
  rw [centered_expansion_pairings none d hd A (by
    intro j hj
    cases j with
    | none => exact (hj rfl).elim
    | some j => exact hA j)]
  have hfilter : (Finset.univ.filter (fun σ : Equiv.Perm (Option J) =>
      σ none = none ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = none)) =
      Finset.univ.filter IsEndpointPairing := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsEndpointPairing]
  rw [hfilter]
  rw [Finset.sum_subtype (p := IsEndpointPairing) (F := inferInstance) _ (by simp)]
  rw [← endpointPairingEquiv.sum_comp (fun σ => d σ.1 * cycleTrace σ.1 A)]
  change (∑ τ : Pairing J, d (endpointPairingPerm τ) *
    cycleTrace (endpointPairingPerm τ) A) = _
  simp_rw [cycleTrace_endpointPairing]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

end Kadison.SchurWeyl
end

end OAI
