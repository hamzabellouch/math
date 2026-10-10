import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSamples
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupSetupWork
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds

namespace OAI

/-! The source-key builder executes all scale/sample loops. Their cost
is bounded using the computed count, which is capped by the arity. -/

namespace EditApproximation.BinaryFraction

def queryGroupSamplesBitBudget (M eM eb eF B : ℕ) : ℕ :=
  let L := 7 + eM + eF
  groupScalesBitBudget eM eb eF + 4 * L +
    L * (L + groupSampleCountBitBudget B + 7 * M + 6) + eb + 4

theorem queryGroupKeySamplesWithWork_bounds (M F Q eM eb eF B : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (cell : ℕ × ℕ)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (heb : eb + 3 ≤ B) (hsb : eM + eb + eF + 7 ≤ B) :
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).1.length ≤
      (7 + eM + eF) * M ∧
    (queryGroupKeySamplesWithWork M F Q eM eb eF hMdef hFdef cell).2 ≤
      queryGroupSamplesBitBudget M eM eb eF B := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hMdef rfl hFdef
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  let indices := queryFinRange scales.1.length (groupDyadicScales M b F).length hlen
  let run := fun scale : Fin (groupDyadicScales M b F).length =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let count := groupSampleCountWithWork M Q b word
    let hc : bitWordValue count.1 = groupSampleCount M Q b (groupDyadicScaleAt M b F scale) := by
      rw [groupSampleCountWithWork_value, queryScaleAt_value]
      rfl
    let coordinates := queryFinRange (bitWordValue count.1)
      (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) hc
    let labeled := arithmeticMapWithWork (fun sample =>
      ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2)) coordinates
    (labeled.1, scales.1.length + count.2 + labeled.2 + coordinates.length + 3)
  have hslen : scales.1.length = 7 + eM + eF := groupScalesWithWork_length eM eb eF
  have hilen : indices.length = 7 + eM + eF := by
    dsimp only [indices]
    rw [queryFinRange_value, List.length_finRange, ← hlen, hslen]
  have hsbounds := groupScalesWithWork_bounds eM eb eF
  have hword (scale : Fin (groupDyadicScales M b F).length) :
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale).width ≤ B := by
    apply (hsbounds.1 _ ?_).trans hsb
    exact List.getElem_mem _
  have hcount (scale : Fin (groupDyadicScales M b F).length) :=
    (groupSampleCountWithWork_bounds M Q b
      (queryScaleAt scales.1 (groupDyadicScales M b F) hs scale) B hM hQ
      (by dsimp only [b]; rw [Nat.size_pow]; omega) (hword scale)).2
  have hrlen (scale : Fin (groupDyadicScales M b F).length) : (run scale).1.length ≤ M := by
    simp only [run, arithmeticMapWithWork_value, List.length_map, queryFinRange_value,
      List.length_finRange]
    exact Nat.min_le_left _ _
  have hrcost (scale : Fin (groupDyadicScales M b F).length) :
      (run scale).2 ≤ (7 + eM + eF) + groupSampleCountBitBudget B + 6 * M + 3 := by
    have hlabel := arithmeticMapWithWork_cost
      (fun sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale)) =>
        ((⟨(b, cell), scale, sample⟩ : GroupScalarKey M F Q), 2))
      (List.finRange _) 2 (fun _ _ => le_rfl)
    simp only [List.length_finRange, Nat.reduceAdd] at hlabel
    have hlen' : groupSampleCount M Q b (groupDyadicScaleAt M b F scale) ≤ M := Nat.min_le_left _ _
    have hlabel' := hlabel.trans (Nat.mul_le_mul_right 5 hlen')
    dsimp only [run]
    simp only [queryFinRange_value, List.length_finRange, hslen]
    have hh := hcount scale
    nlinarith only [hlabel', hh, hlen']
  have hl := arithmeticFlatMapWithWork_length run indices M (fun scale _ => hrlen scale)
  have hc := arithmeticFlatMapWithWork_cost run indices
    ((7 + eM + eF) + groupSampleCountBitBudget B + 6 * M + 3) M
    (fun scale _ => hrcost scale) (fun scale _ => hrlen scale)
  rw [hilen] at hl hc
  constructor
  · exact hl
  · change scales.2 + 4 * scales.1.length + (arithmeticFlatMapWithWork run indices).2 + eb + 4 ≤ _
    rw [hslen]
    have hswork : scales.2 ≤ groupScalesBitBudget eM eb eF := hsbounds.2
    change _ ≤ groupScalesBitBudget eM eb eF + 4 * (7 + eM + eF) +
      (7 + eM + eF) * ((7 + eM + eF) + groupSampleCountBitBudget B + 7 * M + 6) + eb + 4
    rw [show 7 + eM + eF + groupSampleCountBitBudget B + 6 * M + 3 + M + 3 =
      (7 + eM + eF) + groupSampleCountBitBudget B + 7 * M + 6 by omega] at hc
    omega

theorem queryGroupSamplesBitBudget_mono (M eM eb eb' eF B B' : ℕ)
    (he : eb ≤ eb') (hB : B ≤ B') :
    queryGroupSamplesBitBudget M eM eb eF B ≤ queryGroupSamplesBitBudget M eM eb' eF B' := by
  unfold queryGroupSamplesBitBudget groupScalesBitBudget groupSampleCountBitBudget
  dsimp only
  gcongr
  exact Nat.size_le_size he

end EditApproximation.BinaryFraction

end OAI
