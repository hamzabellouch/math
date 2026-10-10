import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkActualRootReferenceFamilyWitness
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverageBudgetDraws

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage
open Construction Conclusion Filter HistoryGiantOriginalMeanFactorization
open HistoryBulkReferenceFrequencyFamily HistoryBulkActualRootReferenceFamily

theorem selected_nested_symbolic_error_eventually
    (d : Decomposition) (Bs BD Bz H : ℝ) (hH : 0 ≤ H) {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k, ∀ (α β : Type*) [Fintype α] [Fintype β]
        (μ : FinitePrior α) (ν : α → FinitePrior β)
        (F G : α → β → Draws (l:=l) C → Draws (l:=l) C →
          RootFrequencyIndex (frequencyBound Bs BD Bz k L) l → ℂ),
      (∀ a, μ.mass a ≠ 0 → ∀ b, (ν a).mass b ≠ 0 → ∀ x y,
        (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).mass x ≠ 0 →
        (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).mass y ≠ 0 → ∀ i,
        ‖F a b x y i-G a b x y i‖ ≤
          pairedChoiceCompensation C (leftChoices C x i) (rightChoices C y i) *
            (30*Real.exp (-Real.exp (ScaleBudget.giant.target*L)))) →
      ‖μ.cmean (fun a => (ν a).cmean (fun b =>
          (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
            (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
              ∑ i, F a b x y i)))) -
        μ.cmean (fun a => (ν a).cmean (fun b =>
          (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
            (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
              ∑ i, G a b x y i))))‖ ≤
        Real.exp (-frequencyBudget Bs BD Bz k L l-H*(bulkSize k L : ℝ)) ∧
      ‖μ.cmean (fun a => (ν a).cmean (fun b =>
          (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
            (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
              ∑ i, F a b x y i)))) -
        μ.cmean (fun a => (ν a).cmean (fun b =>
          (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun x =>
            (internalSourcePrior C.sources (Seed (k:=k) (L:=L)) l).cmean (fun y =>
              ∑ i, G a b x y i))))‖ ≤
        Real.exp (-H*(bulkSize k L : ℝ)) := by
  filter_upwards [selected_nested_choices_error_eventually d Bs BD Bz H hH hk] with L hL
  intro E C hG hcl hcu hb hd l hl α β _ _ μ ν F G hFG
  let F' := fun a b r (c e : Choices (l:=l) C) =>
    F a b (historyDraws C.sources _ _ l c) (historyDraws C.sources _ _ l e)
      (r, historyFrequencies C.sources _ _ l c, historyFrequencies C.sources _ _ l e)
  let G' := fun a b r (c e : Choices (l:=l) C) =>
    G a b (historyDraws C.sources _ _ l c) (historyDraws C.sources _ _ l e)
      (r, historyFrequencies C.sources _ _ l c, historyFrequencies C.sources _ _ l e)
  have h := hL E C hG hcl hcu hb hd l hl α β μ ν F' G' (by
    intro a ha b hb' r c e hc he
    have hc' := hc
    have he' := he
    rw [choicesMass_eq_internalSourcePrior] at hc' he'
    simpa only [F', G', leftChoices, rightChoices, assembleHistoryChoices_projections] using
      hFG a ha b hb' (historyDraws C.sources _ _ l c) (historyDraws C.sources _ _ l e)
        hc' he' (r, historyFrequencies C.sources _ _ l c, historyFrequencies C.sources _ _ l e))
  simpa only [root_choices_sum_eq_source_cmean, F', G',
    historyDraws_assemble, historyFrequencies_assemble] using h

end Ostmann.Arithmetic.HistoryBulkFibreGiantErrorAverage

end

end OAI
