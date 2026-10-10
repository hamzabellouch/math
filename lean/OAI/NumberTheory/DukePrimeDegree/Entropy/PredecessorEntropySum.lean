import OAI.NumberTheory.DukePrimeDegree.Entropy.CountableConditioningChain
import OAI.NumberTheory.DukePrimeDegree.Entropy.FutureLabelBlocks

namespace OAI

/-! # Entropy increments for finite predecessor symbols -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

lemma orbitName_eq_iff_head_future {Y α : Type*} (T : Y → Y) (B : Y → α)
    (N : ℕ) (x y : Y) :
    orbitName T B (N+1) x=orbitName T B (N+1) y ↔
      B x=B y ∧ futureName T B N x=futureName T B N y := by
  constructor
  · intro h
    constructor
    · simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using
        congrFun h (0 : Fin (N+1))
    · funext i
      simpa only [futureName,orbitName,Fin.val_succ,Function.iterate_succ_apply] using
        congrFun h i.succ
  · rintro ⟨hh,ht⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [orbitName,Fin.val_zero,Function.iterate_zero_apply] using hh
    · simpa only [futureName,orbitName,Fin.val_succ,Function.iterate_succ_apply] using
        congrFun ht j

theorem predecessor_word_conditional_increment
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B (N+1))
        (MeasurableSpace.comap (Q ∘ T^[N+1]) inferInstance) =
      conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) +
      conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (futureLabelBlock T Q (N+1)) inferInstance) := by
  let F := Q ∘ T^[N+1]
  let W := futureName T B N
  have hF : Measurable F := hQ.comp (hT.measurable.iterate (N+1))
  have hW : Measurable W := measurable_pi_iff.mpr fun i =>
    hB.comp ((hT.measurable.iterate i.val).comp hT.measurable)
  have hV : Measurable (orbitName T B (N+1)) := measurable_pi_iff.mpr fun i =>
    hB.comp (hT.measurable.iterate i.val)
  have hpair : Measurable (fun y => (W y,B y)) := hW.prodMk hB
  have he : conditionalSigmaEntropy μ (orbitName T B (N+1))
        (MeasurableSpace.comap F inferInstance) =
      conditionalSigmaEntropy μ (fun y => (W y,B y))
        (MeasurableSpace.comap F inferInstance) := by
    apply le_antisymm
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ F hF _ hV _ hpair
      intro x y _ hxy
      exact (orbitName_eq_iff_head_future T B N x y).mpr
        ⟨(congrArg Prod.snd hxy),(congrArg Prod.fst hxy)⟩
    · apply conditionalSigmaEntropy_le_of_fiber_refinement μ F hF _ hpair _ hV
      intro x y _ hxy
      have hh := (orbitName_eq_iff_head_future T B N x y).mp hxy
      exact Prod.ext hh.2 hh.1
  rw [he,conditionalSigmaEntropy_chain_nat μ W
    (fun w => hW (measurableSet_singleton w)) B
    (fun b => hB (measurableSet_singleton b)) F hF]
  congr 1
  · have hVN : Measurable (orbitName T B N) := measurable_pi_iff.mpr fun i =>
      hB.comp (hT.measurable.iterate i.val)
    have h := conditionalSigmaEntropy_comp_preserving_nat μ hT (orbitName T B N)
      (fun w => hVN (measurableSet_singleton w))
      (Q ∘ T^[N]) (hQ.comp (hT.measurable.iterate N))
    change conditionalSigmaEntropy μ (futureName T B N)
      (MeasurableSpace.comap (Q ∘ T^[N+1]) inferInstance) = _
    have hshift : (Q ∘ T^[N]) ∘ T = Q ∘ T^[N+1] := by
      funext x
      exact congrArg Q (Function.iterate_succ_apply T N x).symm
    rw [hshift] at h
    exact h
  · congr 1
    have hs : observationSigma (fun x => (F x,W x))=
        observationSigma (futureLabelBlock T Q (N+1)) := by
      apply le_antisymm
      · apply observationSigma_le_of_fiber_refinement
        intro x y hxy
        have hh := (futureLabelBlock_eq_iff_predecessor_symbols T Q B href decode hdecode N x y).mp hxy
        exact Prod.ext hh.1 hh.2
      · apply observationSigma_le_of_fiber_refinement
        intro x y hxy
        exact (futureLabelBlock_eq_iff_predecessor_symbols T Q B href decode hdecode N x y).mpr
          (Prod.mk.inj hxy)
    rw [observationSigma_pair_eq] at hs
    exact hs

theorem predecessor_word_conditional_sum
    {Y : Type*} [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (Q : Y → ℕ) (hQ : Measurable Q)
    {M : ℕ} (B : Y → Fin (M+1)) (hB : Measurable B)
    (href : ∀ x y, Q x=Q y → Q (T x)=Q (T y) → B x=B y)
    (decode : ℕ → Fin (M+1) → ℕ) (hdecode : ∀ x, decode (Q (T x)) (B x)=Q x)
    (N : ℕ) :
    conditionalSigmaEntropy μ (orbitName T B N)
        (MeasurableSpace.comap (Q ∘ T^[N]) inferInstance) =
      ∑ k ∈ Finset.range N, conditionalSigmaEntropy μ B
        (MeasurableSpace.comap (futureLabelBlock T Q (k+1)) inferInstance) := by
  induction N with
  | zero =>
      simp only [Finset.range_zero,Finset.sum_empty]
      apply le_antisymm
      · have h := conditional_countable_le_observationEntropy μ (orbitName T B 0)
          (orbitName_measurable_fiber hT.measurable
            (fun b => hB (measurableSet_singleton b)) 0) (Q ∘ T^[0])
          (hQ.comp (hT.measurable.iterate 0))
        simpa only [observationEntropy_unique] using h
      · exact conditionalSigmaEntropy_comap_nonneg μ (Q ∘ T^[0])
          (hQ.comp (hT.measurable.iterate 0)) _
          (orbitName_measurable_fiber hT.measurable
            (fun b => hB (measurableSet_singleton b)) 0)
  | succ N ih =>
      rw [predecessor_word_conditional_increment μ hT Q hQ B hB href decode hdecode N,
        ih,Finset.sum_range_succ]

end DukePrimeDegree

end

end OAI
