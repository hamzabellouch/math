import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceListSlotBudget

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical Filter
namespace GlobalRecord

noncomputable def signedAssignedSum {S : PrimeSystem} {B τ C₀ : ℝ}
    (D : S.DivisorFamily B τ C₀) (L h ℓ : ℕ) (hh : 0 < h) (n N : ℕ)
    {T : ℝ} (cut : S.Cutoffs T) : ℝ :=
  ∑ x : GlobalRecord D L h ℓ hh n N,
    assignedKernelIntegral x.line cut x.primitives (recordGroup x.line hh x.primitives x.record)

theorem source_signed_sum_le (h : ℕ) (hh : 0 < h) (τ C₀ : ℝ)
    (hτ : 0 ≤ τ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (T : ℝ) (cut : (sourceSystem B).Cutoffs T),
      signedAssignedSum D (pathLength B) h (sourceLength B) hh (listCutoff B) (exceptionalBudget B) cut ≤
        majorantSum (D:=D) (L:=pathLength B) (h:=h) (ℓ:=sourceLength B) (hh:=hh)
          (n:=listCutoff B) (N:=exceptionalBudget B) T (sourceErrorBound h τ C₀ B) := by
  filter_upwards [source_eventually_large h] with B hB
  intro D T cut
  apply sum_le_sum
  intro x hx
  have ht : (x.primitives.length:ℝ) ≤ 2*B :=
    (by exact_mod_cast x.length_le : (x.primitives.length:ℝ) ≤ (listCutoff B:ℝ)).trans
      (listCutoff_le B hB.1)
  have he := restorationError_source_bound x.line x.primitives x.labels hB.1 hC₀ hτ
    (sourceLength_le B (zero_le_one.trans hB.1)) (pathLength_le B hB.1) ht
    (fun p => (source_prime_lower B hB.1 p).le)
  exact (trace_integration_finite x.line hh cut x.primitives x.record (fun p => (hB.2 p).1)).trans
    (traceIntegrationMajorant_mono x.line hh x.primitives x.record T he)

theorem source_signed_record_summation (h : ℕ) (hh : 0 < h) (τ T C₀ A : ℝ)
    (hτ : 1 ≤ τ) (hC₀ : 0 ≤ C₀) (hA : 0 ≤ A) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T),
      Real.exp (A*(sourceListSlotBudget C₀ B:ℝ)*Real.log B) *
        signedAssignedSum D (pathLength B) h (sourceLength B) hh (listCutoff B) (exceptionalBudget B) cut ≤
          B^(-(1+2*eta)*(sourceLength B:ℝ)) := by
  have he := (sourceErrorBound_tendsto h τ C₀).eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [source_signed_sum_le h hh τ C₀ (zero_le_one.trans hτ) hC₀,
    source_record_sum_with_prefactor τ T C₀ A hτ hC₀ hA,he] with B hs hm he
  intro D cut
  exact (mul_le_mul_of_nonneg_left (hs D T cut) (Real.exp_pos _).le).trans
    (hm D h hh (sourceErrorBound h τ C₀ B) he)

end GlobalRecord
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
