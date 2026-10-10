import OAI.Combinatorics.EditApproximation.Geometry.InitialConeGrid

namespace OAI

/-! The finite representative list and the actual rounded comparison representative. -/

namespace EditApproximation

def representativeList {n : ℕ} (N P F : ℕ) (a : ℚ)
    (initial : TargetInterval n → ℚ) : List (ℕ × TargetInterval n) :=
  (dyadicScales N).flatMap fun b =>
    ((targetStates n).filter fun r => decide
      (seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi ∧
        (b : ℚ) / (4 * a) ≤ initial r ∧ initial r ≤ 8 * F * b)).map fun r => (b, r)

theorem representativeList_mem {n N P F b : ℕ} (a : ℚ)
    (initial : TargetInterval n → ℚ) (r : TargetInterval n)
    (hb : b ∈ dyadicScales N)
    (hgrid : seedGridSpacing b P ∣ r.lo ∧ seedGridSpacing b P ∣ r.hi)
    (hlower : (b : ℚ) / (4 * a) ≤ initial r) (hupper : initial r ≤ 8 * F * b) :
    (b, r) ∈ representativeList N P F a initial := by
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, List.mem_map.mpr ⟨r, List.mem_filter.mpr ⟨targetStates_complete n r, ?_⟩, rfl⟩⟩
  simpa using ⟨hgrid.1, hgrid.2, hlower, hupper⟩

theorem rounded_comparison_representative {α : Type*} (source target : List α)
    (N P F : ℕ) (a : ℚ) (hP : 4 ≤ P) (hF : 0 ≤ (F : ℚ)) (ha : 0 < a)
    (initial : TargetInterval target.length → ℚ)
    (hlower : ∀ r, (stateEditCost source target r : ℚ) / a ≤ initial r)
    (hupper : ∀ r, initial r ≤ 2 * F * stateEditCost source target r)
    (q : TargetInterval target.length) (hc : 0 < stateEditCost source target q)
    (hN : stateEditCost source target q ≤ N) :
    let b := 2 ^ Nat.log 2 (stateEditCost source target q)
    (b, roundInterval (seedGridSpacing b P) q) ∈ representativeList N P F a initial := by
  dsimp only
  let b := 2 ^ Nat.log 2 (stateEditCost source target q)
  let r := roundInterval (seedGridSpacing b P) q
  have hscale := cost_dyadicScale _ N hc hN
  have hscaleLower : (b : ℚ) ≤ stateEditCost source target q := by exact_mod_cast hscale.2.1
  have hscaleUpper : (stateEditCost source target q : ℚ) < 2 * b := by exact_mod_cast hscale.2.2
  have he := rounded_seedGrid_error b P (by omega) q
  have he0 : (0 : ℚ) ≤ targetEndpointDistance q r := Nat.cast_nonneg _
  have hPr : (4 : ℚ) ≤ P := by exact_mod_cast hP
  have hsmall : (targetEndpointDistance q r : ℚ) ≤ b / 2 := by nlinarith only [he, he0, hPr]
  have hdist := abs_le.mp (stateEditCost_distance_abs source target q r)
  have hcrlo : (b : ℚ) / 4 ≤ stateEditCost source target r := by linarith only [hdist.1, hdist.2, hsmall, hscaleLower]
  have hcrhi : (stateEditCost source target r : ℚ) ≤ 4 * b := by
    have hb0 : (0 : ℚ) ≤ b := Nat.cast_nonneg _
    linarith only [hdist.1, hdist.2, hsmall, hscaleUpper, hb0]
  apply representativeList_mem a initial r hscale.1 (roundInterval_on_grid _ q)
  · have hdiv := div_le_div_of_nonneg_right hcrlo ha.le
    have hid : (b : ℚ) / 4 / a = b / (4 * a) := by ring
    rw [hid] at hdiv
    exact hdiv.trans (hlower r)
  · have hmul := mul_le_mul_of_nonneg_left hcrhi (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hF)
    exact (hupper r).trans (by nlinarith only [hmul])

end EditApproximation

end OAI
