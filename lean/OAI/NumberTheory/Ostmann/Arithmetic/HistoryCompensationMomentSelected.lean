import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentSources
import OAI.NumberTheory.Ostmann.Construction.CounterpartNormalizationBoundPriors

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationMoment
open Construction CompensationEqualityPatterns CounterpartNormalizationBound
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : Decomposition} {Bs BD Bz L : ℝ} {k : ℕ} {E : Finset ℕ}

theorem selected_sourceCutoff_le_one (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin p : ℕ) : C.sourceCutoff origin p ≤ 1 := by
  unfold InitialSourceChoice.sourceCutoff initialSourceValue
  split_ifs
  · exact le_rfl
  · exact smoothPartition_le_one _
  · exact smoothPartition_le_one _
  · exact le_rfl

theorem selected_source_mass_mul_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ℕ) (p : (C.sources origin).Sample) :
    (C.sources origin).law.mass p * (p.val : ℝ) ≤ C.sourceNormalization origin := by
  have hp : (p.val : ℝ) ≠ 0 := by
    exact_mod_cast ((C.sources origin).prime p.val p.property).ne_zero
  rw [C.source_mass_normalization, div_mul_cancel₀ _ hp]
  exact (mul_le_mul_of_nonneg_left (selected_sourceCutoff_le_one C origin p.val)
    (sourceNormalization_nonneg C origin)).trans_eq (mul_one _)

omit [DecidableEq ι] in

theorem selected_sourceWeight_mass_mul_le (C : InitialSourceChoice d Bs BD Bz k L E)
    (origin : ι → ℕ) (i : ι) (v : CommonSample C.sources origin) :
    sourceWeight C.sources origin i v * (v.val : ℝ) ≤ C.sourceNormalization (origin i) := by
  unfold sourceWeight
  split_ifs with hv
  · exact selected_source_mass_mul_le C (origin i) ⟨v.val, hv⟩
  · simpa only [zero_mul] using sourceNormalization_nonneg C (origin i)

omit [DecidableEq ι] in
theorem selected_source_block_moment_le {η : Type*} [Fintype η] [DecidableEq η]
    (C : InitialSourceChoice d Bs BD Bz k L E) (origin : ι → ℕ) (pick : η → ι) (j : η) :
    (∑ v : CommonSample C.sources origin, (v.val : ℝ)⁻¹ *
      ∏ i, sourceWeight C.sources origin (pick i) v * (v.val : ℝ)) ≤
      ∏ i ∈ Finset.univ.erase j, C.sourceNormalization (origin (pick i)) := by
  apply block_moment_le _ _ _ j
  · intro i v
    exact sourceWeight_nonneg C.sources origin (pick i) v
  · intro v
    exact_mod_cast (commonSample_prime C.sources origin v).pos
  · intro i v
    exact selected_sourceWeight_mass_mul_le C origin (pick i) v
  · exact sourceWeight_sum C.sources origin (pick j)

end Ostmann.Arithmetic.HistoryCompensationMoment

end

end OAI
