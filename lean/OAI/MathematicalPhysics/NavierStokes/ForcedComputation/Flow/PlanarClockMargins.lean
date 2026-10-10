import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarInitialShift

namespace OAI

/-! Height bounds for whole instruction rectangles, rather than just encoded
points. These bounds supply the clock and observer margins of the routing
segments, including their filled interiors. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows Radix

theorem coordinateMap_nonterminal_vertical (M : Alternating.Machine) (hM : M.WellFormed)
    {x : Plane} (hx : 1 / 4 - (bandScale M : ℝ) / 2 ≤ x 0 ∧
      x 0 ≤ 1 / 4 + (bandScale M : ℝ) / 2) :
    1 / 4 - 3 * (bandScale M : ℝ) / 16 ≤ coordinateMap M hM x 1 ∧
      coordinateMap M hM x 1 ≤ 1 / 4 + 3 * (bandScale M : ℝ) / 16 := by
  have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  change 1 / 4 - 3 * (bandScale M : ℝ) / 16 ≤
      ((43 / 128 : ℚ) : ℝ) - ((11 / 32 : ℚ) : ℝ) * x 0 ∧
    ((43 / 128 : ℚ) : ℝ) - ((11 / 32 : ℚ) : ℝ) * x 0 ≤
      1 / 4 + 3 * (bandScale M : ℝ) / 16
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  constructor <;> nlinarith [hx.1, hx.2]

theorem instruction_source_nonhalting (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) : recorderHalting M b.source = false := by
  have he (q : Control (State M) (Alphabet M)) :
      haltingControl (finiteMachine M hM) q = recorderHalting M q := by
    cases q <;> rfl
  rw [← he]
  exact b.rule.source_nonhalting

theorem instruction_source_vertical (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) :
    1 / 4 - 3 * (bandScale M : ℝ) / 16 ≤ x 1 ∧
      x 1 ≤ 1 / 4 + 3 * (bandScale M : ℝ) / 16 := by
  change x ∈ (PlanarConjugacy.box _ _ _ _ _).carrier at hx
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact coordinateMap_nonterminal_vertical M hM
    (stateBox_nonterminal_x M b.source (instruction_source_nonhalting M hM b)
      (geometricInstruction_source_unit M hM b) hy)

theorem instruction_target_nonterminal_vertical (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (hn : recorderHalting M b.target = false) {x : Plane}
    (hx : x ∈ (instruction M hM b).target.carrier) :
    1 / 4 - 3 * (bandScale M : ℝ) / 16 ≤ x 1 ∧
      x 1 ≤ 1 / 4 + 3 * (bandScale M : ℝ) / 16 := by
  change x ∈ (PlanarConjugacy.box _ _ _ _ _).carrier at hx
  rw [← PlanarConjugacy.box_image (compression_pos M hM) (by norm_num)] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact coordinateMap_nonterminal_vertical M hM
    (stateBox_nonterminal_x M b.target hn (geometricInstruction_target_unit M hM b) hy)

theorem shifted_vertical_band (M : Alternating.Machine) (δ : Fin 2 → ℚ)
    (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) {x : Plane}
    (hx : 1 / 4 - 3 * (bandScale M : ℝ) / 16 ≤ x 1 ∧
      x 1 ≤ 1 / 4 + 3 * (bandScale M : ℝ) / 16) :
    3 / 16 ≤ shiftPoint δ x 1 ∧ shiftPoint δ x 1 ≤ 5 / 16 := by
  have hk := bandScale_le_real M
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hδ
  change 3 / 16 ≤ x 1 + (δ 1 : ℝ) ∧ x 1 + (δ 1 : ℝ) ≤ 5 / 16
  constructor <;> linarith [hx.1, hx.2]

theorem shifted_instruction_source_height (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (δ : Fin 2 → ℚ)
    (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) :
    3 / 16 ≤ shiftPoint δ x 1 ∧ shiftPoint δ x 1 ≤ 5 / 16 :=
  shifted_vertical_band M δ hδ (instruction_source_vertical M hM b hx)

theorem shifted_instruction_target_nonterminal_height
    (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (hn : recorderHalting M b.target = false)
    (δ : Fin 2 → ℚ) (hδ : |(δ 1 : ℝ)| ≤ 3 / 1024) {x : Plane}
    (hx : x ∈ (instruction M hM b).target.carrier) :
    3 / 16 ≤ shiftPoint δ x 1 ∧ shiftPoint δ x 1 ≤ 5 / 16 :=
  shifted_vertical_band M δ hδ (instruction_target_nonterminal_vertical M hM b hn hx)

end ForcedComputation.Recorder.Planar

end

end OAI
