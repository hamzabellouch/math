import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualBlockGeometry
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice
import OAI.Analysis.LipschitzHilbert.Estimates.ErrorSourceBridge

namespace OAI

/-! The manuscript's rounded block parameters bound the number of
residual lengths polynomially, uniformly over the packet family. -/

noncomputable section
open Filter
open scoped Topology
namespace LipschitzHilbert

/-- The actual integer exponent of the source branching is at most L²
for large L; no bound depends on the number of packet scales. -/
theorem eventually_source_block_length_budget :
    ∀ᶠ L : ℝ in atTop,
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ) ≤ L^(2:ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [SourceParameters.eventually_branching_separation,
    eventually_ge_atTop (max 1 (1/(100*Real.log 2)))] with L hsep hlarge
  have hL : 1 ≤ L := (le_max_left _ _).trans hlarge
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hc : 1 ≤ L*(100*Real.log 2) :=
    (div_le_iff₀ (by positivity : 0 < 100*Real.log 2)).mp ((le_max_right _ _).trans hlarge)
  have hlogB : Real.log (SourceParameters.branching L) =
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ)*Real.log 2 := by
    rw [source_branching_eq_two_pow,Real.log_pow]
  have hlog := Real.log_le_log (pow_pos (SourceParameters.branching_pos L) 100) hsep
  rw [Real.log_pow,Real.log_exp,hlogB] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hp : L^(9/10:ℝ) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL
      (by norm_num : (9/10:ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hc hL0.le
  rw [Real.rpow_two]
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 100*Real.log 2)).mp
  nlinarith

namespace SourceLabeledLattice

/-- Every shifted residual block of an actual dyadic packet family has
at most L² lengths for sufficiently large L. -/
theorem eventually_shifted_residual_length_budget :
    ∀ᶠ L : ℝ in atTop,
    ∀ (N : ℕ) (κ : Type) (Label : Fin N → Type) (Item : ∀ j, Label j → Type)
      [Fintype κ] [∀ j l, Fintype (Item j l)]
      (P : SourceLabeledLattice N κ Label Item) (grid : AngularGrid),
      (grid.branching:ℝ) = SourceParameters.step L →
    ∀ (_hK : 0 < SourceParameters.blockCount L) (shift : Fin (SourceParameters.blockCount L))
      (w : ℝ) (hw : 0 < w),
      (∀ j : Fin N, grid.eligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) 0) →
    ∀ block : ℕ,
      let stop := fun j : Fin N => grid.lastEligible
        (grid.rootWidth/(SourceParameters.branching L)^2) (w/P.length j)
        (div_pos hw (P.length_pos j))
      ((residualLengthSet stop (ShiftedBlocks.endpoint shift block)
        (ShiftedBlocks.endpoint shift (block+1))).card:ℝ) ≤ L^(2:ℝ) := by
  filter_upwards [eventually_source_block_length_budget] with L hbudget
  intro N κ Label Item _ _ P grid hbranch hK shift w hw hzero block
  have hcard := grid.source_shifted_residual_length_card L hbranch hK shift hw
    P.topLength_pos hzero block
  have hc : ((residualLengthSet
      (fun j : Fin N => grid.lastEligible (grid.rootWidth/(SourceParameters.branching L)^2)
        (w/P.length j) (div_pos hw (P.length_pos j)))
      (ShiftedBlocks.endpoint shift block) (ShiftedBlocks.endpoint shift (block+1))).card:ℝ) ≤
      ((SourceParameters.stepExponent L*SourceParameters.blockCount L:ℕ):ℝ) := by
    dsimp only [SourceLabeledLattice.length]
    exact_mod_cast hcard
  exact hc.trans hbudget

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
