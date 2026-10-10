import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputs
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupInputCost

namespace OAI

namespace EditApproximation.BinaryFraction

def querySharedCellInputsLength (M exponent eM eF : ℕ) : ℕ :=
  (7 + eM + eF) * queryGroupInputsLength M exponent

def querySharedCellInputsBitBudget (M exponent eM eb eF B R : ℕ) : ℕ :=
  let L := 7 + eM + eF
  groupScalesBitBudget eM eb eF + 4 * L +
    L * (queryGroupInputsBitBudget M exponent B R + L + queryGroupInputsLength M exponent + 4) + eb + 4

theorem querySharedCellInputsBitBudget_mono_eb (M exponent eM eb eb' eF B R : ℕ) (he : eb ≤ eb') :
    querySharedCellInputsBitBudget M exponent eM eb eF B R ≤
      querySharedCellInputsBitBudget M exponent eM eb' eF B R := by
  unfold querySharedCellInputsBitBudget groupScalesBitBudget
  dsimp only
  gcongr
  exact Nat.size_le_size he

theorem querySharedCellInputsWithWork_bounds {nx ny : ℕ} (M F Q eM eb eF : ℕ)
    (hMdef : M = 2 ^ eM) (hFdef : F = 2 ^ eF) (parent : TargetInterval nx)
    (exponent B R : ℕ) (cell : ℕ × ℕ)
    (draw : ∀ scale : Fin (groupDyadicScales M (2 ^ eb) F).length,
      Fin (groupSampleCount M Q (2 ^ eb) (groupDyadicScaleAt M (2 ^ eb) F scale)) → Fin M × ℕ)
    (hB : 4 ≤ B) (hnx : Nat.size nx ≤ B) (hny : Nat.size ny ≤ B)
    (hM : Nat.size M + 2 ≤ B) (hQ : Nat.size Q + 2 ≤ B)
    (heb : eb + 3 ≤ B) (hsb : eM + eb + eF + 7 ≤ B)
    (hc : Nat.size cell.1 ≤ B) (he : exponent + 1 ≤ B)
    (hR : ∀ scale sample, (draw scale sample).2 ≤ R) :
    (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hMdef hFdef parent exponent cell draw).1.length ≤
      querySharedCellInputsLength M exponent eM eF ∧
    (querySharedCellInputsWithWork (ny := ny) M F Q eM eb eF hMdef hFdef parent exponent cell draw).2 ≤
      querySharedCellInputsBitBudget M exponent eM eb eF B R := by
  let b := 2 ^ eb
  let scales := groupScalesWithWork eM eb eF
  have hs : scales.1.map value = groupDyadicScales M b F := by
    simpa only [nat_value] using computedGroupScales_value M b F eM eb eF hMdef rfl hFdef
  have hlen : scales.1.length = (groupDyadicScales M b F).length := by
    simpa only [List.length_map] using congrArg List.length hs
  let indices := queryFinRange scales.1.length (groupDyadicScales M b F).length hlen
  let run := fun scale : Fin (groupDyadicScales M b F).length =>
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    let hv : word.value = groupDyadicScaleAt M b F scale := queryGroupScaleAt_value M b F _ hs scale
    let states := queryGroupInputsTransportWithWork (ny := ny) parent b exponent Q cell word
      (groupDyadicScaleAt M b F scale) hv (draw scale)
    (states.1, states.2 + scales.1.length + 1)
  have hslen : scales.1.length = 7 + eM + eF := groupScalesWithWork_length eM eb eF
  have hilen : indices.length = 7 + eM + eF := by
    dsimp only [indices]
    rw [queryFinRange_value, List.length_finRange, ← hlen, hslen]
  have hscales := groupScalesWithWork_bounds eM eb eF
  have hMpos : 0 < M := by rw [hMdef]; exact Nat.two_pow_pos _
  have hFpos : 0 < F := by rw [hFdef]; exact Nat.two_pow_pos _
  have hrun (scale : Fin (groupDyadicScales M b F).length) :
      (run scale).1.length ≤ queryGroupInputsLength M exponent ∧
      (run scale).2 ≤ queryGroupInputsBitBudget M exponent B R + (7 + eM + eF) + 1 := by
    let word := queryScaleAt scales.1 (groupDyadicScales M b F) hs scale
    have hw : word.width ≤ B := (hscales.1 _ (List.getElem_mem _)).trans hsb
    have hmem : word.value ∈ groupDyadicScales M b F := by
      rw [← hs]
      exact List.mem_map.mpr ⟨word, List.getElem_mem _, rfl⟩
    have hp : 0 < word.value := groupDyadicScales_pos hmem
    have hf : (b : ℚ) / M ≤ word.value := groupDyadicScales_lower hMpos (Nat.two_pow_pos _) hFpos word.value hmem
    have hr := queryGroupInputsWithWork_bounds (ny := ny) parent b exponent Q B R cell word
      (fun sample => draw scale (Fin.cast (congrArg (groupSampleCount M Q b)
        (queryGroupScaleAt_value M b F _ hs scale)) sample)) hB hMpos hnx hny hM hQ
      (by dsimp only [b]; rw [Nat.size_pow]; omega) hc he hw hp.le hf
      (fun sample => hR scale _)
    simpa only [run, word, queryGroupInputsTransportWithWork, hslen] using
      And.intro hr.1 (Nat.add_le_add_right (Nat.add_le_add_right hr.2 scales.1.length) 1)
  have hl := arithmeticFlatMapWithWork_length run indices (queryGroupInputsLength M exponent)
    (fun scale _ => (hrun scale).1)
  have hw := arithmeticFlatMapWithWork_cost run indices
    (queryGroupInputsBitBudget M exponent B R + (7 + eM + eF) + 1)
    (queryGroupInputsLength M exponent) (fun scale _ => (hrun scale).2) (fun scale _ => (hrun scale).1)
  rw [hilen] at hl hw
  rw [show queryGroupInputsBitBudget M exponent B R + (7 + eM + eF) + 1 +
    queryGroupInputsLength M exponent + 3 = queryGroupInputsBitBudget M exponent B R +
    (7 + eM + eF) + queryGroupInputsLength M exponent + 4 by omega] at hw
  have hinputsCost : scales.2 + 4 * scales.1.length +
      (arithmeticFlatMapWithWork run indices).2 + eb + 4 ≤
      querySharedCellInputsBitBudget M exponent eM eb eF B R := by
    rw [hslen]
    have hsc : scales.2 ≤ groupScalesBitBudget eM eb eF := hscales.2
    simpa only [querySharedCellInputsBitBudget] using
      Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.add_le_add (Nat.add_le_add_right hsc (4 * (7 + eM + eF))) hw) eb) 4
  simpa only [querySharedCellInputsWithWork, b, scales, indices, run,
    querySharedCellInputsLength] using And.intro hl hinputsCost

end EditApproximation.BinaryFraction

end OAI
