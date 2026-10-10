import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.NormalizedBranchTrace
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarClockMargins

namespace OAI

/-! Clock and observation margins for the entire filled branch trajectory. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian PlanarRouting Set

/-- The parking rectangles have room for the rational initial translation. -/
theorem shifted_parking_bounds {n : ℕ} {κ : ℚ} (hκ : 0 ≤ κ) (hκ' : κ ≤ 1 / 64)
    (i : Fin n) (δ : Fin 2 → ℚ)
    (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512) (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ (parkingBox n κ i).carrier) :
    translatedPoint δ x ∈ clockRectangle.carrier ∧ 3 / 16 ≤ translatedPoint δ x 1 := by
  have hb := parkingBox_bounds hκ hκ' i hx
  have hs : (parkingScale n : ℝ) ≤ 1 / 64 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (parkingScale_le n)
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hk : (0 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hk' : (κ : ℝ) ≤ 1 / 64 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr hκ'
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hc : (parkingCenter n i 0 : ℝ) < 3 / 4 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr (parkingCenter_bounds n i).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh
  have hxu := (hx 0).2
  change x 0 ≤ ((parkingCenter n i 0 + parkingScale n * κ : ℚ) : ℝ) at hxu
  push_cast at hxu
  have hm := mul_le_mul hs hk' hk (by norm_num : (0 : ℝ) ≤ 1 / 64)
  obtain ⟨hd₀, hd₀'⟩ := abs_le.mp hδ₀
  obtain ⟨hd₁, hd₁'⟩ := abs_le.mp hδ₁
  constructor
  · intro j
    fin_cases j
    · change ((1 / 8 : ℚ) : ℝ) ≤ x 0 + (δ 0 : ℝ) ∧
        x 0 + (δ 0 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      constructor <;> linarith [hb.1]
    · change ((1 / 32 : ℚ) : ℝ) ≤ x 1 + (δ 1 : ℝ) ∧
        x 1 + (δ 1 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      constructor <;> linarith [hb.2.2.1, hb.2.2.2]
  · change 3 / 16 ≤ x 1 + (δ 1 : ℝ)
    linarith [hb.2.2.1]

theorem horizontalPoint_vertical (R : RationalBox 2) (p : Fin 2 → ℚ) (x : Plane) :
    horizontalPoint R p x 1 = x 1 := by
  simp [horizontalPoint, horizontalCenter]

theorem shifted_horizontalPoint_clock (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (R : RationalBox 2)
    (hwidth : R.halfWidth 0 ≤ 1 / 128)
    (δ : Fin 2 → ℚ) (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512)
    (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ R.carrier)
    (hy : (5 / 128 : ℝ) ≤ x 1 ∧ x 1 ≤ 19 / 64) :
    translatedPoint δ (horizontalPoint R (parkingFor M hM b) x) ∈ clockRectangle.carrier := by
  have hc := parkingCenter_bounds (geometricBranches M hM).length (branchIndex M hM b)
  have hcl : (1 / 2 : ℝ) < (parkingFor M hM b 0 : ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.1
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hcu : (parkingFor M hM b 0 : ℝ) < 3 / 4 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr hc.2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh
  have hw := RationalBox.mem_carrier_iff.mp hx 0
  obtain ⟨hwl, hwu⟩ := abs_le.mp hw
  obtain ⟨hd₀, hd₀'⟩ := abs_le.mp hδ₀
  obtain ⟨hd₁, hd₁'⟩ := abs_le.mp hδ₁
  intro j
  fin_cases j
  · change ((1 / 8 : ℚ) : ℝ) ≤
        horizontalPoint R (parkingFor M hM b) x 0 + (δ 0 : ℝ) ∧
      horizontalPoint R (parkingFor M hM b) x 0 + (δ 0 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
    have he : horizontalPoint R (parkingFor M hM b) x 0 =
        x 0 + (parkingFor M hM b 0 : ℝ) - R.center 0 := by
      simp [horizontalPoint, horizontalCenter]
      ring
    rw [he]
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith
  · change ((1 / 32 : ℚ) : ℝ) ≤
        horizontalPoint R (parkingFor M hM b) x 1 + (δ 1 : ℝ) ∧
      horizontalPoint R (parkingFor M hM b) x 1 + (δ 1 : ℝ) ≤ ((7 / 8 : ℚ) : ℝ)
    rw [horizontalPoint_vertical]
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor <;> linarith [hy.1, hy.2]

theorem branch_scaledStage_mem (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {x : Plane}
    (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 5) :
    scaledStage (instruction M hM b) (parkingScale (geometricBranches M hM).length)
      (3 / 8) (parkingFor M hM b) x k ∈
        (parkingBox (geometricBranches M hM).length (bandScale M) (branchIndex M hM b)).carrier := by
  have hw := instruction_halfWidths M hM b
  exact scaledStage_mem_parking (bandScale_pos M).le (branchIndex M hM b) _
    (instruction_factor_pos M hM b) (instruction_image M hM b)
    hw.1 hw.2.1 hw.2.2.1 hw.2.2.2 hx k

theorem shifted_branchAnchors_clock (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (δ : Fin 2 → ℚ)
    (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512) (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 9) :
    translatedPoint δ (branchAnchors M hM b x k) ∈ clockRectangle.carrier := by
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hs := instruction_source_bounds M hM b hx
  have ht' := instruction_target_bounds M hM b ht
  have hw := instruction_halfWidthQ_bound M hM b
  have hws : (instruction M hM b).source.halfWidth 0 ≤ 1 / 128 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (hw.1 0)
    simpa only [halfWidthQ_cast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have hwt : (instruction M hM b).target.halfWidth 0 ≤ 1 / 128 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (hw.2 0)
    simpa only [halfWidthQ_cast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hh
  have hp (j : Fin 5) := (shifted_parking_bounds (bandScale_pos M).le (bandScale_le M)
    (branchIndex M hM b) δ hδ₀ hδ₁ (branch_scaledStage_mem M hM b hx j)).1
  fin_cases k
  · exact shifted_coding_rectangle_clock M hM δ hδ₀ hδ₁ hs
  · exact shifted_horizontalPoint_clock M hM b _ hws δ hδ₀ hδ₁ hx hs.2
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact hp 3
  · exact hp 4
  · exact shifted_horizontalPoint_clock M hM b _ hwt δ hδ₀ hδ₁ ht ht'.2
  · exact shifted_coding_rectangle_clock M hM δ hδ₀ hδ₁ ht'

theorem shifted_branchAnchors_safe (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (hn : recorderHalting M b.target = false)
    (δ : Fin 2 → ℚ) (hδ₀ : |(δ 0 : ℝ)| ≤ 1 / 512) (hδ₁ : |(δ 1 : ℝ)| ≤ 3 / 1024)
    {x : Plane} (hx : x ∈ (instruction M hM b).source.carrier) (k : Fin 9) :
    3 / 16 ≤ translatedPoint δ (branchAnchors M hM b x k) 1 := by
  have ht : (instruction M hM b).affine x ∈ (instruction M hM b).target.carrier := by
    rw [← instruction_image M hM b]
    exact mem_image_of_mem _ hx
  have hs := (shifted_instruction_source_height M hM b δ hδ₁ hx).1
  have ht' := (shifted_instruction_target_nonterminal_height M hM b hn δ hδ₁ ht).1
  have hp (j : Fin 5) := (shifted_parking_bounds (bandScale_pos M).le (bandScale_le M)
    (branchIndex M hM b) δ hδ₀ hδ₁ (branch_scaledStage_mem M hM b hx j)).2
  fin_cases k
  · exact hs
  · change 3 / 16 ≤ horizontalPoint _ _ x 1 + (δ 1 : ℝ)
    rw [horizontalPoint_vertical]
    exact hs
  · exact hp 0
  · exact hp 1
  · exact hp 2
  · exact hp 3
  · exact hp 4
  · change 3 / 16 ≤ horizontalPoint _ _ ((instruction M hM b).affine x) 1 + (δ 1 : ℝ)
    rw [horizontalPoint_vertical]
    exact ht'
  · exact ht'

theorem normalizedAnchors_clock (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 9) : normalizedAnchors I hI b x k ∈ clockRectangle.carrier := by
  have hδ := initialShift_small (freshInput I) (freshInput_valid hI) (fresh_initial_nonhalting I hI)
  exact shifted_branchAnchors_clock _ _ b _ hδ.1 hδ.2 hx k

theorem normalizedAnchors_safe (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hn : recorderHalting (freshMachine I.1) b.target = false)
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 9) : 3 / 16 ≤ normalizedAnchors I hI b x k 1 := by
  have hδ := initialShift_small (freshInput I) (freshInput_valid hI) (fresh_initial_nonhalting I hI)
  exact shifted_branchAnchors_safe _ _ b hn _ hδ.1 hδ.2 hx k

theorem normalizedCurve_segment (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (x : Plane) (k : Fin 8) (t : ℝ) :
    normalizedCurve I hI b x k t = normalizedAnchors I hI b x k.castSucc +
      smoothRamp (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
        (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).start
        (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
        (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).finish t •
      (normalizedAnchors I hI b x k.succ - normalizedAnchors I hI b x k.castSucc) := by
  unfold normalizedCurve branchCurve
  rw [Pulse.curve, Primitive.path_segment, branchCurve_endpoint]
  ext j
  simp only [translatedPoint, normalizedAnchors, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem normalizedCurve_clock (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 8) (t : ℝ) : normalizedCurve I hI b x k t ∈ clockRectangle.carrier := by
  have h₀ := normalizedAnchors_clock I hI b hx k.castSucc
  have h₁ := normalizedAnchors_clock I hI b hx k.succ
  have hθ := smoothRamp_range
    (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
      (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).start
    (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
      (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).finish t
  rw [normalizedCurve_segment]
  intro j
  have hj₀ := h₀ j
  have hj₁ := h₁ j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  constructor <;> nlinarith [hθ.1, hθ.2]

theorem normalizedCurve_safe (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (b : Branch (finiteMachine (freshMachine I.1) (freshInput_valid hI).1))
    (hn : recorderHalting (freshMachine I.1) b.target = false)
    {x : Plane} (hx : x ∈ (instruction (freshMachine I.1) (freshInput_valid hI).1 b).source.carrier)
    (k : Fin 8) (t : ℝ) : 3 / 16 ≤ normalizedCurve I hI b x k t 1 := by
  have h₀ := normalizedAnchors_safe I hI b hn hx k.castSucc
  have h₁ := normalizedAnchors_safe I hI b hn hx k.succ
  have hθ := smoothRamp_range
    (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
      (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).start
    (compiledPulse (freshMachine I.1) (freshInput_valid hI).1
      (branchIndices (freshMachine I.1) (freshInput_valid hI).1 b k)).finish t
  rw [normalizedCurve_segment]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  nlinarith [hθ.1, hθ.2]

end ForcedComputation.Recorder.Planar

end

end OAI
