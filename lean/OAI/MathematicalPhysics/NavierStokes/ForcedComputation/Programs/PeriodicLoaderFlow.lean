import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.PeriodicLoaderGeometry
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderSubprogramFlow

namespace OAI

/-! The periodically repeated loading row is used once. Every later material
step belongs to the fresh recorder, whose orbit never returns to that row. -/

noncomputable section
namespace ForcedComputation.Recorder
open ShearFlows Radix Set

def periodicStartingPoint : Space := ![1 / 4, 1 / 2, 1 / 4]

theorem periodicLoader_center (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    (periodicLoaderInstruction I hI).affine (fun j => (periodicLoaderStart j : ℝ)) =
      fun j => (initialPointQ I hI j : ℝ) := by
  funext j
  fin_cases j <;>
    simp [periodicLoaderInstruction, Instruction.affine, centeredBox_center]

theorem periodicLoader_contains (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    (fun j => (periodicLoaderStart j : ℝ)) ∈ (periodicLoaderInstruction I hI).source.carrier := by
  intro j
  change ((periodicLoaderStart j - periodicLoaderRadius I.1 : ℚ) : ℝ) ≤ _ ∧
    _ ≤ ((periodicLoaderStart j + periodicLoaderRadius I.1 : ℚ) : ℝ)
  have hr : (0 : ℝ) < periodicLoaderRadius I.1 := by
    exact_mod_cast div_pos (bandScale_pos I.1) (by norm_num : (0 : ℚ) < 8)
  simp only [Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith

theorem periodicLoading_endpoint (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (periodicInitializedInput I hI).period
      (periodicInitializedInput I hI).realizingVelocity Φ) :
    Φ 1 periodicStartingPoint =
      atHeight (codedPoint (freshMachine I.1)
        (finiteInitializedRecorder (freshInput I) (freshInput_valid hI))) (1 / 4) := by
  let d := periodicInitializedInput I hI
  let b := periodicLoaderInstruction (freshInput I) (freshInput_valid hI)
  have hd := periodicInitializedInput_valid I hI
  have hb : b ∈ d.instructions := by
    simp [d, b, periodicInitializedInput, periodicLoadedInput, loadedInput, Input.withInstructions]
  have hc := periodicLoader_contains (freshInput I) (freshInput_valid hI)
  have hδ : (0 : ℝ) < d.tubeRadius := by exact_mod_cast tubeRadius_pos hd
  have ht := sourceTube_contains b d.codingHeight hδ
    (Set.mem_image_of_mem (fun X => atHeight X d.codingHeight) hc)
  have he := realizingVelocity_periodMap hd hΦ hb ht
  rw [atHeight_horizontal, periodicLoader_center, initialPointQ_spec] at he
  simpa [d, periodicStartingPoint, periodicLoaderStart, atHeight] using he

theorem Steps.flow_loaded {I : Alternating.MachineInput}
    {hI : Alternating.ValidInput I} {n : ℕ}
    {C : Configuration (State (freshMachine I.1)) (Alphabet (freshMachine I.1))}
    (h : Steps (finiteMachine (freshMachine I.1) (freshInput_valid hI).1) n
      (finiteInitializedRecorder (freshInput I) (freshInput_valid hI)) C)
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (periodicInitializedInput I hI).period
      (periodicInitializedInput I hI).realizingVelocity Φ) :
    Φ (n + 1) periodicStartingPoint = atHeight (codedPoint (freshMachine I.1) C) (1 / 4) := by
  have he := h.flow_nat_in (periodicInitializedInput_valid I hI)
    (fun m E hc b hb _ _ => periodicLoadedInput_used_mem I hI hc b hb) hΦ
  have hs := hΦ.nat_shift (realizingVelocity_time_periodic _) 1 (n : ℝ) periodicStartingPoint
  norm_num only [Nat.cast_one] at hs
  rw [hs, periodicLoading_endpoint I hI hΦ]
  simpa only [periodicInitializedInput_height, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] using he

theorem periodicLoading_safe (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow (periodicInitializedInput I hI).period
      (periodicInitializedInput I hI).realizingVelocity Φ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ t periodicStartingPoint 0 < 1 / 2 := by
  let M := freshMachine I.1
  let hv := freshInput_valid hI
  let d := periodicInitializedInput I hI
  let b := periodicLoaderInstruction (freshInput I) hv
  have hb : b ∈ d.instructions := by
    simp [d, b, periodicInitializedInput, periodicLoadedInput, loadedInput, Input.withInstructions]
  have hc := periodicLoader_contains (freshInput I) hv
  have hkpos : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
  have hfirst : codedPoint M (finiteInitializedRecorder (freshInput I) hv) 0 ≤
      1 / 4 + (bandScale M : ℝ) / 2 := by
    rw [codedPoint_first]
    have hh : recorderHalting M (finiteInitializedRecorder (freshInput I) hv).control = false := by
      change (freshMachine I.1).isHalting 0 = false
      exact freshMachine_not_halting_zero I.1
    rw [hh]
    simp only [Bool.false_eq_true, ite_false]
    have hB : (1 : ℝ) < radixBase M := by exact_mod_cast radixBase_gt_one M
    have hd : ∀ a, (0 : ℝ) ≤ radixDigit M a ∧
        (radixDigit M a : ℝ) ≤ (radixBase M : ℝ) - 1 := by
      intro a
      exact ⟨(radixDigit_bounds M a).1, by linarith [(radixDigit_bounds M a).2]⟩
    have he := encode_mem_unit hB hd
      (tapeAt (finiteInitializedRecorder (freshInput I) hv)).1
    have hk : (0 : ℝ) < bandScale M := by exact_mod_cast bandScale_pos M
    nlinarith [he.2]
  have he := materialFlow_first_le_of_mem (periodicInitializedInput_valid I hI) hΦ hb hc
    (a := 1 / 4 + (bandScale M : ℝ) / 2)
    (by simp only [b, periodicLoaderInstruction, centeredBox_center, periodicLoaderStart,
          Matrix.cons_val_zero, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
        linarith)
    (by
      change (centeredBox (initialPointQ (freshInput I) hv)
        (periodicLoaderRadius (freshMachine I.1))).center 0 ≤ _
      rw [centeredBox_center, congrFun (initialPointQ_spec (freshInput I) hv) 0]
      exact hfirst) ht
  have hk := bandScale_le_real M
  change _ ≤ _ + 2 * ((bandScale M / 2 : ℚ) : ℝ) at he
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at he
  have hp : atHeight (fun j => (periodicLoaderStart j : ℝ)) (d.codingHeight : ℝ) =
      periodicStartingPoint := by simp [d, periodicStartingPoint, periodicLoaderStart, atHeight]
  rw [hp] at he
  linarith

end ForcedComputation.Recorder

end

end OAI
