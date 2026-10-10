import OAI.Combinatorics.EditApproximation.Queries.QuerySharedGeometrySpace
import OAI.Combinatorics.EditApproximation.Queries.QueryInputSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupInputs
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem signedPowerTwoAllocation_le_work (e : ℤ) :
    signedPowerTwoAllocation e ≤ (signedPowerTwoWithWork e).2 := by
  unfold signedPowerTwoAllocation signedPowerTwoWithWork
  split_ifs <;> dsimp only <;> exact Nat.le_succ _



theorem groupScalesAllocation_le_work (eM eb eF : ℕ) :
    groupScalesAllocation eM eb eF ≤ (groupScalesWithWork eM eb eF).2 := by
  have h := arithmeticMapAllocation_le_work signedPowerTwoWithWork signedPowerTwoAllocation
    (integerClosedRange ((eb : ℤ) - eM) ((6 + eF + eb : ℕ) : ℤ))
    (fun e _ => signedPowerTwoAllocation_le_work e)
  unfold groupScalesAllocation groupScalesWithWork
  dsimp only
  omega



theorem queryGroupLabelsAllocation_le_work (M Q b : ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b h.value) → ℕ)
    (ha : ∀ i, allocation i ≤ (draw i).2) :
    queryGroupLabelsAllocation M Q b h draw allocation ≤ (queryGroupLabelsWithWork M Q b h draw).2 := by
  have costBound (c c' t t' a a' l : ℕ) (hc : c ≤ c') (ht : t ≤ t')
      (ha : a + l ≤ a') : c + t + (a + 2 * l) ≤ c' + t' + a' + l + 2 := by
    omega
  have hc := groupSampleCountAllocation_le_work M Q b h
  have ht := naturalEqualAllocation_le_work (bitWordValue (groupSampleCountWithWork M Q b h).1) M
  have hm := arithmeticMapAllocation_with_spine draw allocation
    (queryFinRange (bitWordValue (groupSampleCountWithWork M Q b h).1)
      (groupSampleCount M Q b h.value) (groupSampleCountWithWork_value M Q b h)) (fun i _ => ha i)
  unfold queryGroupLabelsAllocation queryGroupLabelsWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact (Nat.add_le_add_right (Nat.add_le_add hc ht) M).trans (Nat.le_add_right _ 2)
  · exact costBound _ _ _ _ _ _ _ hc ht hm



theorem queryGroupInputsAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (b exponent Q : ℕ) (cell : ℕ × ℕ) (h : BinaryFraction)
    (draw : Fin (groupSampleCount M Q b h.value) → Fin M × ℕ)
    (allocation : Fin (groupSampleCount M Q b h.value) → ℕ)
    (ha : ∀ i, allocation i ≤ (draw i).2) :
    queryGroupInputsAllocation (ny := ny) parent b exponent Q cell h draw allocation ≤
      (queryGroupInputsWithWork (ny := ny) parent b exponent Q cell h draw).2 := by
  let build := fun i : Fin M =>
    let states := queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h
    let tagged := arithmeticMapWithWork (fun r => ((i, r), 1)) states.1
    (tagged.1, states.2 + tagged.2 + 1)
  have hl := queryGroupLabelsAllocation_le_work M Q b h draw allocation ha
  have hg := arithmeticFlatMapAllocation_le_work build
    (fun i => queryGroupRoundedStatesAllocation (ny := ny) parent b exponent cell i h +
      arithmeticMapAllocation (fun _ => 1) (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1)
    (queryGroupLabelsWithWork M Q b h draw).1 (by
      intro i _
      have hs := queryGroupRoundedStatesAllocation_le_work (ny := ny) parent b exponent cell i h
      have hm := arithmeticMapAllocation_le_work (fun r => ((i, r), 1)) (fun _ => 1)
        (queryGroupRoundedStatesWithWork (ny := ny) parent b exponent cell i h).1 (fun _ _ => le_rfl)
      dsimp only [build]
      omega)
  unfold queryGroupInputsAllocation queryGroupInputsWithWork
  dsimp only [build] at hg ⊢
  omega

end EditApproximation.BinaryFraction

end OAI
