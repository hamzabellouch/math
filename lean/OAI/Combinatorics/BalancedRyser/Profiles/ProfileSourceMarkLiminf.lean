import OAI.Combinatorics.BalancedRyser.Profiles.ProfileSourceMarkLimit

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology BigOperators

namespace Balanced.ProfileSourceMarkLimit

open ProfileScheduledMarks ProfileScheduledMargin ProfileClassMargin

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]

theorem normalizedMean_nonneg (D C : Finset (Line K)) (η ε : ℝ) :
    0 ≤ normalizedMean D C η ε := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.expect_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem normalizedMean_le (k : ℕ) (D C : Finset (Line K))
    (hp : IsProfilePair k D C) (η ε : ℝ) :
    normalizedMean D C η ε ≤ 2 * (k : ℝ) + 1 := by
  have hq : (0 : ℝ) < Fintype.card K := by
    exact_mod_cast Fintype.card_pos (α := K)
  apply (div_le_iff₀ hq).mpr
  apply le_trans _ (ProfileMarkedError.population_size_le k D C hp)
  apply Finset.expect_le Finset.univ_nonempty
  intro p _
  exact_mod_cast sourceMarkCount_le D C η ε p

theorem cutoffMass_le_liminf_sourceTest
    (k : ℕ) (hk : 1 ≤ k) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A)
    (hgap : ∃ a : ℝ, 0 < a ∧ ProfileClassSizeGap a A)
    {F : ℕ → Type u} [∀ t, Field (F t)] [∀ t, Fintype (F t)]
    [∀ t, DecidableEq (F t)]
    (D C : ∀ t, Finset (Line (F t)))
    (hA : ∀ t, A (F t) (D t) (C t))
    (hq : Tendsto (fun t => Fintype.card (F t)) atTop atTop)
    {c : ℝ} {P : Profile} {νD νC : FiniteMeasure Profile}
    (hlim : ProfileSequenceLimit D C c P νD νC) (n : ℕ) :
    cutoffMass P νD νC n ≤
      atTop.liminf (fun t => sourceTest n (F t) (D t) (C t)) := by
  have hbounded : atTop.IsBoundedUnder (· ≤ ·)
      (fun t => sourceTest n (F t) (D t) (C t)) :=
    isBoundedUnder_of ⟨2 * (k : ℝ) + 1, fun t =>
      normalizedMean_le k (D t) (C t) (hvalid (F t) (D t) (C t) (hA t)) _ _⟩
  have hnonneg : atTop.IsBoundedUnder (· ≥ ·)
      (fun t => sourceTest n (F t) (D t) (C t)) :=
    isBoundedUnder_of ⟨0, fun t => normalizedMean_nonneg (D t) (C t) _ _⟩
  apply (le_liminf_iff hbounded.isCobounded_ge hnonneg).mpr
  intro r hr
  exact source_limitLowerBound k hk A hvalid hgap F D C hA hq c P νD νC hlim n r hr

end Balanced.ProfileSourceMarkLimit

end

end OAI
