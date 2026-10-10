import Mathlib

namespace OAI

universe u

noncomputable section
namespace Problem313
open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Delete a distinguished coordinate to reindex all supports containing it. -/
theorem sum_supports_containing (i : ι) (a : Finset ι → ℝ) :
    (∑ S : Finset ι, if i ∈ S then a S else 0) =
      ∑ S : Finset ι, if i ∉ S then a (insert i S) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij' (fun S _ => S.erase i) (fun S _ => insert i S) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    simp
  · intro S hS
    simp
  · intro S hS
    exact Finset.insert_erase (Finset.mem_filter.mp hS).2
  · intro S hS
    exact Finset.erase_insert (Finset.mem_filter.mp hS).2
  · intro S hS
    rw [Finset.insert_erase (Finset.mem_filter.mp hS).2]

/-- Algebraic coordinate energy identity from the derivative Fourier identities. -/
theorem spectral_coordinate_energy (i : ι) (a b : Finset ι → ℝ) (σ : ℝ)
    (hzero : ∀ S, i ∈ S → b S = 0)
    (hinsert : ∀ S, i ∉ S → a (insert i S) = σ * b S) :
    (∑ S : Finset ι, if i ∈ S then (a S)^2 else 0) =
      σ^2 * ∑ S : Finset ι, (b S)^2 := by
  rw [sum_supports_containing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hi : i ∈ S
  · simp [hi, hzero S hi]
  · simp [hi, hinsert S hi, mul_pow]

/-- Counting each spectral support once for every coordinate it contains. -/
theorem sum_card_mul_eq_sum_mem (a : Finset ι → ℝ) :
    (∑ S : Finset ι, (S.card : ℝ) * a S) =
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp [Finset.sum_ite_mem, nsmul_eq_mul]

/-- Summing coordinate energies gives the finite Dirichlet identity. -/
theorem spectral_dirichlet (a : Finset ι → ℝ) (I : ι → ℝ) (σ : ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι, if i ∈ S then (a S)^2 else 0) = σ^2 * I i) :
    (∑ S : Finset ι, (S.card : ℝ) * (a S)^2) = σ^2 * ∑ i, I i := by
  rw [sum_card_mul_eq_sum_mem]
  simp_rw [hcoord]
  rw [Finset.mul_sum]

end Problem313

end

end OAI
