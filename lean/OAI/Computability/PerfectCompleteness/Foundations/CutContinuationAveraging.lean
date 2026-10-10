import OAI.Computability.PerfectCompleteness.Construction.OriginalHiddenChild
import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCutBridge

namespace OAI

section

namespace PerfectCompleteness.CutContinuationAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem sigmaLaw_pushforward {E Γ : Type*} {F : E → Type*}
    [Fintype E] [∀ e, Fintype (F e)] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : ∀ e, FiniteDistribution (F e))
    (f : ∀ e, F e → Γ) :
    (CompletionSoundness.sigmaLaw μ ν).pushforward (fun x => f x.1 x.2) =
      μ.mixture (fun e => (ν e).pushforward (f e)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward, CompletionSoundness.sigmaLaw,
    FiniteDistribution.mixture, Fintype.sum_sigma, Finset.mul_sum, mul_ite, mul_zero]

private theorem product_mixture_pushforward {E A B Γ : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype Γ]
    (μ : FiniteDistribution A) (κ : FiniteDistribution E)
    (ν : E → FiniteDistribution B) (f : A × B → Γ) :
    (μ.product (κ.mixture ν)).pushforward f =
      κ.mixture (fun e => (μ.product (ν e)).pushforward f) := by
  have hp : μ.product (κ.mixture ν) = κ.mixture (fun e => μ.product (ν e)) := by
    apply FiniteDistribution.eq_of_weight_eq
    intro x
    simp only [FiniteDistribution.product, FiniteDistribution.mixture, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    exact mul_left_comm _ _ _
  rw [hp, FiniteDistribution.pushforward_mixture]

private theorem sigma_product_observe {E A B Γ : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A)
    (observe : A → B) (f : E × B → Γ) :
    (CompletionSoundness.sigmaLaw μ (fun _ => ν)).pushforward
        (fun z => f (z.1, observe z.2)) =
      (μ.product (ν.pushforward observe)).pushforward f := by
  have hp : (μ.product ν).pushforward (fun z => (z.1, observe z.2)) =
      μ.product (ν.pushforward observe) := by
    simpa only [FiniteDistribution.pushforward_id, id_eq] using
      FiniteDistribution.product_pushforward μ ν id observe
  rw [← hp, FiniteDistribution.pushforward_comp]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward, CompletionSoundness.sigmaLaw,
    FiniteDistribution.product, Fintype.sum_sigma, Fintype.sum_prod_type]

variable {branch : Nat → Nat} {n m t : Nat}

def originalArrayLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) : FiniteDistribution (Arrays slots rows) :=
  (GeometricPath.law (m + 1) hbranch).mixture (fun leaf =>
    WholeArraySampler.law rows repeats (p.append (GeometricPath.leafPath leaf)) slots)

theorem observed_sourceLaw_eq_mixture (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) :
    (OriginalHiddenChild.sourceLaw calls rows repeats slots hbranch).pushforward
        (OriginalHiddenChild.observed calls rows repeats slots) =
      (GeometricPath.law (m + 1) hbranch).mixture (fun leaf =>
        (OriginalChildBlocks.sourceLaw calls rows repeats leaf.1
          (GeometricPath.leafPath leaf.2) slots).pushforward
            (OriginalChildBlocks.observed calls rows repeats leaf.1
              (GeometricPath.leafPath leaf.2) slots)) := by
  unfold OriginalHiddenChild.sourceLaw OriginalHiddenChild.observed
  exact sigmaLaw_pushforward
    (E := Slots branch (m + 1))
    (F := fun leaf => OriginalChildBlocks.SourceTape calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots)
    (Γ := CutChildGrouping.Assembled (C := Fin calls) slots rows)
    (GeometricPath.law (m + 1) hbranch)
    (fun leaf => OriginalChildBlocks.sourceLaw calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots)
    (fun leaf tape => OriginalChildBlocks.observed calls rows repeats leaf.1
      (GeometricPath.leafPath leaf.2) slots tape)

theorem originalArrayLaw_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) :
    originalArrayLaw rows repeats p slots hbranch =
      ((exteriorLaw rows repeats p slots).product
        ((OriginalHiddenChild.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
          rows repeats (cutSlots p slots) hbranch).pushforward
            (OriginalHiddenChild.observed (OriginalCutCalls.count rows repeats n (m + 1))
              rows repeats (cutSlots p slots)))).pushforward
                (OriginalWholeCutBridge.reconstruct rows repeats p slots) := by
  symm
  rw [observed_sourceLaw_eq_mixture, product_mixture_pushforward]
  apply congrArg ((GeometricPath.law (m + 1) hbranch).mixture)
  funext leaf
  exact OriginalWholeCutBridge.reconstruct_child_law rows repeats p leaf.1
    (GeometricPath.leafPath leaf.2) slots

theorem originalArrayLaw_eq_sigma (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (hbranch : ∀ k < m + 1, 0 < branch k) :
    originalArrayLaw rows repeats p slots hbranch =
      (CompletionSoundness.sigmaLaw (exteriorLaw rows repeats p slots) (fun _ =>
        OriginalHiddenChild.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
          rows repeats (cutSlots p slots) hbranch)).pushforward
            (fun z => OriginalWholeCutBridge.reconstruct rows repeats p slots
              (z.1, OriginalHiddenChild.observed (OriginalCutCalls.count rows repeats n (m + 1))
                rows repeats (cutSlots p slots) z.2)) := by
  rw [originalArrayLaw_eq]
  exact (sigma_product_observe (exteriorLaw rows repeats p slots)
    (OriginalHiddenChild.sourceLaw (OriginalCutCalls.count rows repeats n (m + 1))
      rows repeats (cutSlots p slots) hbranch)
    (OriginalHiddenChild.observed (OriginalCutCalls.count rows repeats n (m + 1))
      rows repeats (cutSlots p slots))
    (OriginalWholeCutBridge.reconstruct rows repeats p slots)).symm

end
end PerfectCompleteness.CutContinuationAveraging

end

end OAI
