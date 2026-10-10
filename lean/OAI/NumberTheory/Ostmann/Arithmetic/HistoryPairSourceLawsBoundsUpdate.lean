import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsBoundsMixed
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairSourceLawsUpdate

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryPairSourceLaws
open Construction CompensationEqualityPatterns HistorySelectedFlagMassBounds
attribute [local instance] Classical.propDecidable
variable {ι ρ η : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ]
  [Fintype η] [DecidableEq η]

omit [DecidableEq ι] in

theorem blockNaturalWeight_bounds (sources : SourceFamily) (origin : ι → ℕ)
    {τ : ι → ℕ} (p : Pattern τ) (q : Block p) {k : ℕ} {L : ℝ}
    (hb : Bounds k L (biasedBlockWeight sources origin p q)) :
    SupportBounds k L (commonCandidates sources origin)
      (blockNaturalWeight sources origin p q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    unfold blockNaturalWeight
    split_ifs with hn
    · exact hb.nonneg ⟨n, hn⟩
    · exact le_rfl
  · have he := blockNaturalWeight_sum sources origin p q (fun _ => 1)
    simp only [mul_one] at he
    rw [← he]
    exact hb.mass
  · intro n
    unfold blockNaturalWeight
    split_ifs with hn
    · exact hb.atom ⟨n, hn⟩
    · exact (Real.exp_pos _).le

omit [Fintype η] [Fintype ρ] [DecidableEq ρ] in

theorem dummyMass_bounds (giants : Bool → PrimeSource) (roots : ρ → PrimeSource)
    (sources : SourceFamily) (origin : ι → ℕ) {τ : ι → ℕ} (p : Pattern τ)
    (e : SourceIndex ρ (Block p) ≃ η) (q : Block p) {k : ℕ} {L : ℝ}
    (hg : ∀ b, Bounds k L (giants b).law.mass)
    (hr : ∀ i, Bounds k L (roots i).law.mass)
    (hb : ∀ q, Bounds k L (biasedBlockWeight sources origin p q))
    (hd : Bounds k L (sourceWeight sources origin (blockAnchor p q).val))
    (i : η) :
    SupportBounds k L (mixedSupport giants roots sources origin p (e.symm i))
      (dummyMass giants roots sources origin p e q i) := by
  classical
  by_cases hi : i = e (.inr (.inr q))
  · subst i
    simp only [dummyMass, Function.update_self, e.symm_apply_apply]
    exact integerWeight_bounds _ (common_integerValue_injective sources origin) _ hd
  · simp only [dummyMass, Function.update_of_ne hi]
    exact mixedMass_bounds giants roots sources origin p hg hr hb (e.symm i)

end Ostmann.Arithmetic.HistoryPairSourceLaws

end

end OAI
