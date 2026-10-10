import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceFlagReplacementBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceFlagReplacement
open Construction CompensationEqualityPatterns HistoryPairSourceLaws
attribute [local instance] Classical.propDecidable
variable {ι ρ η : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq η]

omit [DecidableEq ι] in
theorem biasedBlockWeight_nonneg [_decidableEqIndex : DecidableEq ι]
    (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (v : CommonSample sources origin) :
    0 ≤ biasedBlockWeight sources origin p q v := by
  unfold biasedBlockWeight
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply mul_nonneg _ (pow_nonneg (Nat.cast_nonneg _) _)
  exact Finset.prod_nonneg (fun i _ => sourceWeight_nonneg sources origin i.val v)

theorem blockNaturalWeight_nonneg (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) (n : ℕ) :
    0 ≤ blockNaturalWeight sources origin p q n := by
  unfold blockNaturalWeight
  split_ifs
  · exact biasedBlockWeight_nonneg sources origin p q _
  · exact le_rfl

theorem mixedWeight_nonneg (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) (v : mixedCarrier giants roots sources origin p i) :
    0 ≤ mixedWeight giants roots sources origin p i v := by
  rcases i with i | i | q
  · exact (giants i).law.mass_nonneg v
  · exact (roots i).law.mass_nonneg v
  · exact biasedBlockWeight_nonneg sources origin p q v

theorem mixedMass_nonneg (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (i : SourceIndex ρ (Block p)) (z : ℤ) :
    0 ≤ mixedMass giants roots sources origin p i z := by
  unfold mixedMass integerWeight
  apply Finset.sum_nonneg
  intro v hv
  split_ifs
  · exact mixedWeight_nonneg giants roots sources origin p i v
  · exact le_rfl

theorem dummyMass_nonneg (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) (i : η) (z : ℤ) :
    0 ≤ dummyMass giants roots sources origin p e q i z := by
  unfold dummyMass
  by_cases hi : i=e (.inr (.inr q))
  · subst i
    rw [Function.update_self]
    unfold integerWeight
    apply Finset.sum_nonneg
    intro v hv
    split_ifs
    · exact sourceWeight_nonneg sources origin (blockAnchor p q).val v
    · exact le_rfl
  · rw [Function.update_of_ne hi]
    exact mixedMass_nonneg giants roots sources origin p _ z

end Ostmann.Arithmetic.HistoryPairSourceFlagReplacement

end

end OAI
