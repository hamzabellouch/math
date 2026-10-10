import Mathlib
import OAI.Analysis.Commutator.CycleInvariants2
import OAI.Analysis.Commutator.PairTrace
import OAI.Analysis.Commutator.PairTrace2

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

variable {J I : Type*} [Fintype J] [LinearOrder J] [Fintype I] [DecidableEq I]

def pairingCycleEquiv (σ : Pairing J) : cycleSet σ.val ≃ Pairing.Representatives σ where
  toFun := Quotient.lift (fun j => ⟨Pairing.repr σ j, Pairing.repr_lt_apply σ j⟩)
    (fun _ _ h => Subtype.ext (constant_on_cycle σ.val (Pairing.repr σ)
      (Pairing.repr_apply σ) h))
  invFun r := cycleMap σ.val r
  left_inv q := by
    refine Quotient.inductionOn q (fun j => ?_)
    change cycleMap σ.val (Pairing.repr σ j) = cycleMap σ.val j
    rcases le_total j (σ j) with h | h
    · rw [Pairing.repr, min_eq_left h]
    · rw [Pairing.repr, min_eq_right h]
      exact cycleMap_apply σ.val j
  right_inv r := by
    apply Subtype.ext
    exact Pairing.repr_representative σ r

lemma cycleCount_pairing (σ : Pairing J) :
    cycleCount σ.val = Fintype.card (Pairing.Representatives σ) :=
  Fintype.card_congr (pairingCycleEquiv σ)

theorem rawCycleTrace_pairing {𝕜 : Type*} [CommRing 𝕜]
    (σ : Pairing J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ.val A =
      ∏ r : Pairing.Representatives σ, Matrix.trace (A r * A (σ r)) := by
  rw [rawCycleTrace_eq_sum]
  rw [Pairing.sum_prod_pairs σ A]
  apply Finset.prod_congr rfl
  intro r _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

theorem cycleTrace_pairing (σ : Pairing J) (A : J → Matrix I I ℂ) :
    cycleTrace σ.val A =
      ∏ r : Pairing.Representatives σ,
        (Fintype.card I : ℂ)⁻¹ * Matrix.trace (A r * A (σ r)) := by
  rw [cycleTrace, cycleCount_pairing, rawCycleTrace_pairing, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

end Kadison.SchurWeyl
end

end OAI
