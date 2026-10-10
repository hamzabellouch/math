import Mathlib
import OAI.Analysis.Commutator.CycleInvariants
import OAI.Analysis.Commutator.EndpointElimination
import OAI.Analysis.Commutator.EndpointElimination2
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

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem endpoint_coefficient_bound {I : Type*} [Fintype I] [DecidableEq I]
    (a : J) (b : J → I) (hb : Function.Injective b)
    (F : (J → Matrix I I ℂ) → ℂ) (c : Equiv.Perm J → ℂ) (C : ℝ)
    (hF : ∀ A, F A = ∑ σ, c σ * cycleTrace σ A)
    (hbound : ∀ A, ‖F A‖ ≤ C * matrixL1 (A a) *
      ∏ j ∈ Finset.univ.erase a, matrixL2 (A j)) (σ : Equiv.Perm J) :
    ‖c σ‖ * ((Fintype.card I : ℝ)⁻¹) ^ cycleCount σ ≤
      C * (Fintype.card I : ℝ)⁻¹ *
        (Real.sqrt (Fintype.card I : ℝ)⁻¹) ^ (Fintype.card J - 1) := by
  classical
  let A : J → Matrix I I ℂ := fun j => Matrix.single (b (σ j)) (b j) 1
  have he : F A = c σ * ((Fintype.card I : ℂ)⁻¹) ^ cycleCount σ := by
    rw [hF]
    simp only [A, cycleTrace_single b hb, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hh := hbound A
  rw [he, norm_mul, norm_pow, norm_inv, Complex.norm_natCast] at hh
  simpa only [A, matrixL1_single, matrixL2_single, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ] using hh

theorem endpoint_coefficients_vanish
    (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]
    (a : J) (b : ∀ n, J → I n) (hb : ∀ n, Function.Injective (b n))
    (F : ∀ n, (J → Matrix (I n) (I n) ℂ) → ℂ)
    (c : Equiv.Perm J → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ n A, F n A = ∑ σ, c σ * cycleTrace σ A)
    (hbound : ∀ n A, ‖F n A‖ ≤ C * matrixL1 (A a) *
      ∏ j ∈ Finset.univ.erase a, matrixL2 (A j))
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
  exact square_endpoint_unit_bound ‖c σ‖ C (Fintype.card (I n)) (Fintype.card J)
    (cycleCount σ) (norm_nonneg _) hC hI hp
    (endpoint_coefficient_bound a (b n) (hb n) (F n) c C (hF n) (hbound n) σ)

end Kadison.SchurWeyl
end

end OAI
