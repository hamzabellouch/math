import OAI.Geometry.Kahler.HartogsTransfer

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology Metric
open scoped ContDiff NNReal
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs
open BaseConstruction

theorem controlled_potential : ControlledPotential := by
  obtain ⟨S⟩ := exists_testSystem
  let L := (5*Real.log (S.Q:ℝ))/S.d+1
  have hlog : 0 < Real.log (S.Q:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < S.Q by have := S.Q_ge; omega))
  have hd := S.d_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hamp : 5*Real.log (S.Q:ℝ) < L*S.d := by
    dsimp [L]
    rw [add_mul,div_mul_cancel₀ _ S.d_pos.ne']
    linarith [S.d_pos]
  obtain ⟨C,hcontrol,hjets⟩ := basePotential_chart_control S.a S.eps_pos.ne' S.D_ge hL.le S.Q_ge S.P S.separated
  exact ⟨basePotential S.P S.a S.ε L S.Q,C,
    basePotential_contDiffOn S.a L S.eps_pos.ne' S.D_ge S.Q_ge S.P S.separated,
    hcontrol,hjets,S.noMinorant hL hamp⟩

theorem main_theorem : MainTheorem := main_of_controlledPotential controlled_potential

end PinchedHartogs

end

end OAI
