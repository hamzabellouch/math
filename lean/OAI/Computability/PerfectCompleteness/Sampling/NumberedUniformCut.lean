import OAI.Computability.PerfectCompleteness.Foundations.OriginalWholeCutBridge
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Sampling.OriginalUniformCut

namespace OAI

section

namespace PerfectCompleteness.NumberedUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

private theorem sigma_product_pushforward {E A Γ : Type*}
    [Fintype E] [Fintype A] [Fintype Γ]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A) (f : E × A → Γ) :
    (CompletionSoundness.sigmaLaw μ (fun _ => ν)).pushforward
        (fun z => f (z.1, z.2)) =
      (μ.product ν).pushforward f := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  simp only [FiniteDistribution.pushforward, CompletionSoundness.sigmaLaw,
    FiniteDistribution.product, Fintype.sum_sigma, Fintype.sum_prod_type]

variable {branch : Nat → Nat} {n m t : Nat}

def numberRecordEquiv (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Record rows repeats p slots ≃ OriginalWholeCutBridge.NumberedRecord rows repeats p slots :=
  Equiv.prodCongr (Equiv.refl (Exterior rows repeats p slots))
    ((Equiv.prodCongr
      (Equiv.arrowCongr (callNumbering rows repeats p) (Equiv.refl (H (cutSlots p slots))))
      (Equiv.refl (BelowArrays rows p slots))).trans
        (OriginalWholeCutBridge.assembledEquiv
          (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots)))

@[simp] theorem numberRecordEquiv_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    numberRecordEquiv rows repeats p slots record =
      OriginalWholeCutBridge.numberRecord rows repeats p slots record := rfl

theorem reference_numberRecord_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots) =
      (exteriorLaw rows repeats p slots).product
        (FiniteDistribution.uniform (CutChildGrouping.Assembled
          (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows)) := by
  rw [OriginalUniformCut.referenceLaw_uniform]
  change (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
    (numberRecordEquiv rows repeats p slots) = _
  rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  exact WholeCutSampler.uniform_product.symm

theorem reconstruct_product_uniform (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
        (FiniteDistribution.uniform (CutChildGrouping.Assembled
          (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows))).pushforward
      (OriginalWholeCutBridge.reconstruct rows repeats p slots) =
        WholeArraySampler.law rows repeats p slots := by
  rw [← reference_numberRecord_law rows repeats p slots, FiniteDistribution.pushforward_comp]
  have hmap : (fun record : Record rows repeats p slots =>
      OriginalWholeCutBridge.reconstruct rows repeats p slots
        (OriginalWholeCutBridge.numberRecord rows repeats p slots record)) =
      reconstructRecord rows repeats p slots :=
    funext (OriginalWholeCutBridge.reconstruct_numberRecord rows repeats p slots)
  rw [hmap]
  exact OriginalUniformCut.reconstruct_referenceLaw rows repeats p slots

theorem reconstruct_sigma_uniform (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (CompletionSoundness.sigmaLaw (exteriorLaw rows repeats p slots) (fun _ =>
      FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows))).pushforward
      (fun z => OriginalWholeCutBridge.reconstruct rows repeats p slots (z.1, z.2)) =
        WholeArraySampler.law rows repeats p slots := by
  rw [sigma_product_pushforward]
  exact reconstruct_product_uniform rows repeats p slots

end
end PerfectCompleteness.NumberedUniformCut

end

end OAI
