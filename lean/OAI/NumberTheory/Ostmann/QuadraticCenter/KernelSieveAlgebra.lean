import OAI.NumberTheory.Ostmann.QuadraticCenter.KernelSieveCount
import OAI.NumberTheory.Ostmann.QuadraticSieveHeathBrown

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators

lemma kernelCoefficientInterval_subset (N : ℕ) :
    kernelCoefficientInterval N ⊆ oddSquarefreeUpTo N := by
  intro s hs
  obtain ⟨hs,hfree,hodd⟩ := Finset.mem_filter.mp hs
  obtain ⟨hpos,hle⟩ := Finset.mem_Icc.mp hs
  exact mem_oddSquarefreeUpTo.mpr ⟨by omega,hle,hodd,hfree⟩

lemma kernel_sieve_card_algebra {U N : ℕ} {δ C E K B α : ℝ} {k : ℕ}
    (hU : U ≤ N) (hδ : 0 < δ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hcount : (δ^k/2)^2*K ≤ C*((U:ℝ)*N)^α*((U:ℝ)+N)*E)
    (hbudget : (N:ℝ)*E*(2/δ^k)^2 ≤ B) :
    K ≤ 2*C*((U:ℝ)*N)^α*B := by
  have hδk : 0 < δ^k := pow_pos hδ _
  have hinv : 0 ≤ (2/δ^k)^2 := sq_nonneg _
  have hcancel : (δ^k/2)^2*(2/δ^k)^2=1 := by field_simp
  have hh := mul_le_mul_of_nonneg_right hcount hinv
  have hUn : (U:ℝ) ≤ N := by exact_mod_cast hU
  have hp : 0 ≤ ((U:ℝ)*N)^α := Real.rpow_nonneg (by positivity) _
  calc
    K = ((δ^k/2)^2*K)*(2/δ^k)^2 := by rw [mul_assoc, mul_comm K, ←mul_assoc,hcancel,one_mul]
    _ ≤ (C*((U:ℝ)*N)^α*((U:ℝ)+N)*E)*(2/δ^k)^2 := hh
    _ ≤ (C*((U:ℝ)*N)^α*(2*N)*E)*(2/δ^k)^2 := by gcongr; linarith
    _ = 2*C*((U:ℝ)*N)^α*((N:ℝ)*E*(2/δ^k)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

end Ostmann.QuadraticCenter

end

end OAI
