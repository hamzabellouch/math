import OAI.Computability.PerfectCompleteness.Construction.OriginalChildScalarAssemblyLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas
import OAI.Computability.PerfectCompleteness.Repetition.CutChildCleanLawLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedCleanRate

open ChildBlockCardinality ProjectedCleanRate

noncomputable section

theorem zeroProbability_lower (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) :
    1 / (bound branch height t calls rows : ℝ) ≤
      zeroProbability branch height t calls rows := by
  let ids : RecursiveSpaces.Slots branch height → Fin t → Nat := fun _ _ => 0
  rw [← raw_zero_probability branch height t calls rows ids,
    CleanTreeFactors.rawLaw_uniform]
  exact cleanLowerBound_le_probability
    (slots := ProjectedCardinality.projectedSlots ids)

theorem conservative_coefficient_le {calls budget cost : Nat}
    (hcalls : calls ≤ budget) (hcost : 0 < cost)
    (branch : Nat → Nat) (height t : Nat) (rows : Nat → Nat) :
    FixedBranching.cleanRate cost (bound branch height t budget rows : ℝ) ≤
      coefficient cost branch height t calls rows := by
  have hbound : (bound branch height t calls rows : ℝ) ≤
      (bound branch height t budget rows : ℝ) := by
    exact_mod_cast FixedCallBudget.child_bound_mono hcalls branch height t rows
  have hpositive : (0 : ℝ) < bound branch height t calls rows :=
    Nat.cast_pos.mpr (shape_bound_pos branch height t calls rows)
  have hzero : 1 / (bound branch height t budget rows : ℝ) ≤
      zeroProbability branch height t calls rows :=
    (one_div_le_one_div_of_le hpositive hbound).trans
      (zeroProbability_lower branch height t calls rows)
  have hden : (0 : ℝ) < 48000 * cost := by
    have : (0 : ℝ) < cost := by exact_mod_cast hcost
    positivity
  calc
    _ = (1 / (bound branch height t budget rows : ℝ)) / (48000 * cost) := by
      unfold FixedBranching.cleanRate
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hzero hden.le

theorem decay_le_conservative {calls budget cost cube : Nat}
    (hcalls : calls ≤ budget) (hcost : 0 < cost) (hcube : 2 ≤ cube)
    (branch : Nat → Nat) (height t : Nat) (rows : Nat → Nat) :
    (1 - coefficient cost branch height t calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) ≤
      (1 - FixedBranching.cleanRate cost
        (bound branch height t budget rows : ℝ) / (cube : ℝ) ^ 2) ^ (cube ^ 3) := by
  have hc : (2 : ℝ) ≤ cube := by exact_mod_cast hcube
  have hsquare : (1 : ℝ) ≤ (cube : ℝ) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < (cube : ℝ) ^ 2 := by positivity
  have hcoef := (coefficient_bounds hcost branch height t calls rows).2
  have hbase : 0 ≤ 1 - coefficient cost branch height t calls rows / (cube : ℝ) ^ 2 := by
    have := (div_le_one hden).mpr (hcoef.trans hsquare)
    linarith
  apply pow_le_pow_left₀ hbase
  have h := div_le_div_of_nonneg_right
    (conservative_coefficient_le hcalls hcost branch height t rows) hden.le
  linarith

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

theorem actual_clean_error {calls : Nat} (hcalls : calls ≤ FixedParameters.calls p.plan)
    (height : Nat) :
    (1 - coefficient p.alphabetCost (FixedParameters.branch p) height
      (FixedRows.sourceLength p.plan hδ) calls (FixedRows.rows p.plan) /
        (p.cubeSize height : ℝ) ^ 2) ^ (p.cubeSize height ^ 3) < p.accuracy := by
  have hdecay := decay_le_conservative hcalls p.alphabetCost_pos
    (p.cube_errors height).1 (FixedParameters.branch p) height
    (FixedRows.sourceLength p.plan hδ) (FixedRows.rows p.plan)
  exact hdecay.trans_lt (p.cube_errors height).2.2.2.2

end
end PerfectCompleteness.FixedCleanRate

end

end OAI
