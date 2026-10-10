import OAI.Combinatorics.EditApproximation.Refinement.ComputedQueryRawWork
import OAI.Combinatorics.EditApproximation.Binary.BitQueryNormalizationCost

namespace OAI

namespace EditApproximation
open Filter BinaryFraction
attribute [local instance] queryArityNeZero queryRoundsNeZero
attribute [local irreducible] computedQueryRawWorkDegree computedQueryRawWidthDegree

def computedQueryWorkDegree : ℕ :=
  max computedQueryRawWorkDegree (computedQueryNormalizationDegree computedQueryRawWidthDegree) + 1

/-- Complete local work, including binary denominator normalization. -/
theorem computedQueryLocalWork_cap :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ),
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      (∀ z ∈ source, z < 2 ^ symbolBits) → (∀ z ∈ target, z < 2 ^ symbolBits) →
      target.length ≤ 2 ^ positionBits → occurrence = occurrenceBuild symbolBits positionBits target.zipIdx →
      ∀ key, computedQueryLocalWork source target N occurrence symbolBits positionBits input key ≤
        computedLocalKernelBudget computedQueryWorkDegree N := by
  filter_upwards [computedQueryMemoRaw_bounds, computedQueryNormalizationBudget_cap computedQueryRawWidthDegree,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)]
    with N hraw hnorm hN hell
  intro source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  have hH : 64 ≤ inputHeight N := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hJ : intervalTreeDepth (integerParameters N).M source.length ≤ inputHeight N := by
    have h := computed_tree_depth_bound N source.length hN (by omega) hell
    nlinarith only [h, hell]
  have hr : queryFamilyMemoRemaining (R := inputHeight N ^ 2) target N (integerParameters N).P
      (inputSmallLog N) (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80) key ≤ inputHeight N := by
    cases key with
    | inl key => exact Nat.zero_le _
    | inr key =>
      cases key with
      | inl entry => exact Nat.zero_le _
      | inr request => exact (Nat.sub_le _ _).trans hJ
  have hb : (computedQueryBase N).length ≤ inputHeight N ^ 3 := by
    have h := computed_refinementBase_length N (inputSmallLog N).bits (bitWordValue_bits _)
    have hs : Nat.size (inputSmallLog N) ≤ inputHeight N :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
    have hp2 : 10 * inputHeight N + 3 ≤ inputHeight N ^ 2 := by nlinarith only [hH]
    have hp3 := Nat.pow_le_pow_right (by omega : 0 < inputHeight N) (by decide : 2 ≤ 3)
    exact h.trans ((show 10 * Nat.size (inputSmallLog N) + 3 ≤ inputHeight N ^ 2 by omega).trans hp3)
  have hraw' := hraw source target hsize input occurrence symbolBits positionBits hsb hpb hs ht hp hoc key
  have hlocal := rankedNormalizeBody_localWork_bound (SourceRanked.rank ChargedPhysicalRequest.rank)
    (computedQueryMemoRaw source target N occurrence symbolBits positionBits input)
    (computedQueryBase N) (computedQueryBase_pos N)
    (queryFamilyMemoRemaining target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80))
    (fun _ => computedLocalKernelBudget computedQueryRawWidthDegree N)
    (fun _ => computedLocalKernelBudget computedQueryRawWorkDegree N)
    (inputHeight N ^ 3) hb key hraw'.2 hraw'.1
  have hn := hnorm _ _ _ hr le_rfl (Nat.le_refl (computedLocalKernelBudget computedQueryRawWidthDegree N))
  let D := max computedQueryRawWorkDegree (computedQueryNormalizationDegree computedQueryRawWidthDegree)
  have hrawD := computedLocalKernelBudget_mono N computedQueryRawWorkDegree D (Nat.le_max_left _ _)
  have hnormD := computedLocalKernelBudget_mono N (computedQueryNormalizationDegree computedQueryRawWidthDegree) D
    (Nat.le_max_right _ _)
  have hone : 1 ≤ computedLocalKernelBudget D N := one_le_pow₀ (by omega)
  exact hlocal.trans (computedLocalKernelBudget_three N D _ _ _ (by omega) hrawD (hn.trans hnormD) hone)

end EditApproximation

end OAI
