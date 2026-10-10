import Mathlib
import OAI.Analysis.Commutator.CycleInvariants
import OAI.Analysis.Commutator.EndpointElimination
import OAI.Analysis.Commutator.EndpointElimination3

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

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem endpoint_coefficients_vanish_of_rank_one
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    (a : J) (b : ∀ n, J → I n) (hb : ∀ n, Function.Injective (b n))
    (F : ∀ n, (J → Matrix (I n) (I n) ℂ) → ℂ)
    (c : Equiv.Perm J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n A, F n A = ∑ σ, c σ * cycleTrace σ A)
    (hbound : ∀ n (σ : Equiv.Perm J), ‖F n (fun j => Matrix.single (b n (σ j)) (b n j) 1)‖ ≤
      C * (Fintype.card (I n) : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card (I n) : ℝ)⁻¹) ^ (Fintype.card J - 1))
    (hunbounded : ∀ B : ℕ, ∃ n, B ≤ Fintype.card (I n))
    (σ : Equiv.Perm J) (hσ : 2 * cycleCount σ < Fintype.card J + 1) : c σ = 0 := by
  refine coefficient_zero_of_unbounded_stages
    (c σ) C (Fintype.card J) (cycleCount σ) (fun n => Fintype.card (I n))
    hunbounded ?_ hσ
  intro n
  have hI : 0 < (Fintype.card (I n) : ℝ) := by
    have : Nonempty (I n) := ⟨b n a⟩
    exact_mod_cast Fintype.card_pos
  have hp : 1 ≤ Fintype.card J := by
    have : Nonempty J := ⟨a⟩
    exact Fintype.card_pos
  apply square_endpoint_unit_bound ‖c σ‖ C (Fintype.card (I n)) (Fintype.card J)
    (cycleCount σ) (norm_nonneg _) hC hI hp
  have he : F n (fun j => Matrix.single (b n (σ j)) (b n j) 1) =
      c σ * ((Fintype.card (I n) : ℂ)⁻¹) ^ cycleCount σ := by
    rw [hF]
    simp only [cycleTrace_single (b n) (hb n), mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hh := hbound n σ
  simpa only [he, norm_mul, norm_pow, norm_inv, Complex.norm_natCast] using hh

end Kadison.SchurWeyl
end

end OAI
