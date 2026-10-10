import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarProgram

namespace OAI

/-! Uniform chart margins for every filled tube and parking box in the finite
planar compiler. These bounds concern the whole rectangles, including points
which do not encode tapes. -/

namespace ForcedComputation.PlanarRouting

open ShearFlows

def Between (R : RationalBox 2) (l u : ℚ) : Prop :=
  ∀ j, l ≤ R.lower j ∧ R.upper j ≤ u

theorem endpoints_of_carrier {R : RationalBox 2} (hR : R.positive)
    {l u : ℚ} (h : ∀ x ∈ R.carrier, ∀ j, (l : ℝ) ≤ x j ∧ x j ≤ u) :
    Between R l u := by
  have hl : (fun j => (R.lower j : ℝ)) ∈ R.carrier := by
    intro j
    exact ⟨le_rfl, (Rat.cast_le (K := ℝ)).mpr (hR j).le⟩
  have hu : (fun j => (R.upper j : ℝ)) ∈ R.carrier := by
    intro j
    exact ⟨(Rat.cast_le (K := ℝ)).mpr (hR j).le, le_rfl⟩
  intro j
  exact ⟨(Rat.cast_le (K := ℝ)).mp (h _ hl j).1,
    (Rat.cast_le (K := ℝ)).mp (h _ hu j).2⟩

theorem centerQ_between {R : RationalBox 2} (hR : R.positive)
    {l u : ℚ} (h : Between R l u) (j : Fin 2) :
    l ≤ centerQ R j ∧ centerQ R j ≤ u := by
  have hp := hR j
  have hb := h j
  dsimp [centerQ]
  constructor <;> linarith

theorem recenter_between {R : RationalBox 2} {p : Fin 2 → ℚ}
    (hp : ∀ j, (1 / 32 : ℚ) ≤ p j ∧ p j ≤ 3 / 4)
    (hw : ∀ j, halfWidthQ R j ≤ 1 / 128) :
    Between (recenter R p) (1 / 64) (7 / 8) := by
  intro j
  have h := hp j
  have h' := hw j
  change 1 / 64 ≤ p j - halfWidthQ R j ∧ p j + halfWidthQ R j ≤ 7 / 8
  constructor <;> linarith

@[simp] theorem recenter_halfWidthQ (R : RationalBox 2) (p : Fin 2 → ℚ) (j : Fin 2) :
    halfWidthQ (recenter R p) j = halfWidthQ R j := by
  dsimp [halfWidthQ, recenter]
  ring

theorem translationTube_between {R : RationalBox 2} {p : Fin 2 → ℚ}
    {l u : ℚ} (hR : Between R l u) (hp : Between (recenter R p) l u) :
    Between (translationTube R p) l u := by
  intro j
  exact ⟨le_min (hR j).1 (hp j).1, max_le (hR j).2 (hp j).2⟩

theorem between_mono {R : RationalBox 2} {l l' u u' : ℚ}
    (h : Between R l u) (hl : l' ≤ l) (hu : u ≤ u') : Between R l' u' := by
  intro j
  exact ⟨hl.trans (h j).1, (h j).2.trans hu⟩

end ForcedComputation.PlanarRouting

namespace ForcedComputation.Recorder.Planar

open ShearFlows PlanarRouting PlanarHamiltonian

theorem instruction_endpoint_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    Between (instruction M hM b).source (1 / 32) (1 / 3) ∧
      Between (instruction M hM b).target (1 / 32) (1 / 3) := by
  have he : (compression M hM : ℝ) ≤ 1 / 64 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (compression_le M hM)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  constructor
  · apply endpoints_of_carrier (instruction_source_positive M hM b)
    intro x hx j
    obtain ⟨hx₀, hx₁, hx₂⟩ := instruction_source_bounds M hM b hx
    obtain ⟨hl, hu⟩ := abs_le.mp hx₀
    fin_cases j <;> norm_num <;> constructor <;> linarith
  · apply endpoints_of_carrier (instruction_target_positive M hM b)
    intro x hx j
    obtain ⟨hx₀, hx₁, hx₂⟩ := instruction_target_bounds M hM b hx
    obtain ⟨hl, hu⟩ := abs_le.mp hx₀
    fin_cases j <;> norm_num <;> constructor <;> linarith

theorem instruction_halfWidthQ_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) :
    (∀ j, halfWidthQ (instruction M hM b).source j ≤ 1 / 128) ∧
      (∀ j, halfWidthQ (instruction M hM b).target j ≤ 1 / 128) := by
  have he : (compression M hM : ℝ) ≤ 1 / 64 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (compression_le M hM)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hk : (bandScale M : ℝ) ≤ 1 / 64 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have hk₀ : (0 : ℝ) ≤ bandScale M := by exact_mod_cast (bandScale_pos M).le
  have hh := instruction_halfWidths M hM b
  have hm := mul_le_mul he hk hk₀ (by norm_num : (0 : ℝ) ≤ 1 / 64)
  have hs₀ : (instruction M hM b).source.halfWidth 0 ≤ 1 / 128 := by linarith [hh.1]
  have hs₁ : (instruction M hM b).source.halfWidth 1 ≤ 1 / 128 := by linarith [hh.2.2.1]
  have ht₀ : (instruction M hM b).target.halfWidth 0 ≤ 1 / 128 := by linarith [hh.2.1]
  have ht₁ : (instruction M hM b).target.halfWidth 1 ≤ 1 / 128 := by linarith [hh.2.2.2]
  constructor <;> intro j
  · apply (Rat.cast_le (K := ℝ)).mp
    rw [halfWidthQ_cast]
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    fin_cases j
    · change (instruction M hM b).source.halfWidth 0 ≤ _
      exact hs₀
    · change (instruction M hM b).source.halfWidth 1 ≤ _
      exact hs₁
  · apply (Rat.cast_le (K := ℝ)).mp
    rw [halfWidthQ_cast]
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    fin_cases j
    · change (instruction M hM b).target.halfWidth 0 ≤ _
      exact ht₀
    · change (instruction M hM b).target.halfWidth 1 ≤ _
      exact ht₁

theorem parkingFor_between (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) (j : Fin 2) :
    (1 / 32 : ℚ) ≤ parkingFor M hM b j ∧ parkingFor M hM b j ≤ 3 / 4 := by
  have h := parkingCenter_bounds (geometricBranches M hM).length (branchIndex M hM b)
  fin_cases j
  · exact ⟨by change 1 / 32 ≤ parkingCenter _ _ 0; linarith [h.1], h.2.le⟩
  · change 1 / 32 ≤ 3 / 4 ∧ (3 / 4 : ℚ) ≤ 3 / 4
    norm_num

theorem horizontalCenter_between (M : Alternating.Machine) (hM : M.WellFormed)
    (b : Branch (finiteMachine M hM)) {R : RationalBox 2}
    (hR : R.positive) (hB : Between R (1 / 32) (1 / 3)) (j : Fin 2) :
    (1 / 32 : ℚ) ≤ horizontalCenter R (parkingFor M hM b 0) j ∧
      horizontalCenter R (parkingFor M hM b 0) j ≤ 3 / 4 := by
  fin_cases j
  · exact parkingFor_between M hM b 0
  · have h := centerQ_between hR hB 1
    change 1 / 32 ≤ centerQ R 1 ∧ centerQ R 1 ≤ 3 / 4
    exact ⟨h.1, h.2.trans (by norm_num)⟩

theorem phaseRectangle_between {R S P : RationalBox 2} {p : Fin 2 → ℚ}
    (hR : R.positive) (hS : S.positive)
    (hs : Between R (1 / 32) (1 / 3)) (ht : Between S (1 / 32) (1 / 3))
    (hws : ∀ j, halfWidthQ R j ≤ 1 / 128) (hwt : ∀ j, halfWidthQ S j ≤ 1 / 128)
    (hp : ∀ j, (1 / 32 : ℚ) ≤ p j ∧ p j ≤ 3 / 4)
    (hP : Between P (1 / 64) (7 / 8)) (phase : Phase) :
    Between (phaseRectangle R S p P phase) (1 / 64) (7 / 8) := by
  have hc {T : RationalBox 2} (hT : T.positive) (hB : Between T (1 / 32) (1 / 3)) :
      ∀ j, (1 / 32 : ℚ) ≤ horizontalCenter T (p 0) j ∧
        horizontalCenter T (p 0) j ≤ 3 / 4 := by
    intro j
    fin_cases j
    · exact hp 0
    · have h := centerQ_between hT hB 1
      change 1 / 32 ≤ centerQ T 1 ∧ centerQ T 1 ≤ 3 / 4
      exact ⟨h.1, h.2.trans (by norm_num)⟩
  have hcs := hc hR hs
  have hct := hc hS ht
  cases phase with
  | extractHorizontal =>
      exact translationTube_between (between_mono hs (by norm_num) (by norm_num)) (recenter_between hcs hws)
  | extractVertical =>
      apply translationTube_between (recenter_between hcs hws)
      exact recenter_between hp (by simpa only [recenter_halfWidthQ] using hws)
  | scale k => exact hP
  | insertVertical =>
      apply translationTube_between (recenter_between hp hwt)
      exact recenter_between hct (by simpa only [recenter_halfWidthQ] using hwt)
  | insertHorizontal =>
      apply translationTube_between (recenter_between hct hwt)
      have he : recenter (recenter S (horizontalCenter S (p 0))) (centerQ S) = S := by
        apply box_ext
        · funext j
          change centerQ S j - halfWidthQ (recenter S (horizontalCenter S (p 0))) j = S.lower j
          rw [recenter_halfWidthQ, centerQ_sub_halfWidthQ]
        · funext j
          change centerQ S j + halfWidthQ (recenter S (horizontalCenter S (p 0))) j = S.upper j
          rw [recenter_halfWidthQ, centerQ_add_halfWidthQ]
      rw [he]
      exact between_mono ht (by norm_num) (by norm_num)

theorem Action.rectangle_between {M : Alternating.Machine} {hM : M.WellFormed}
    (a : Action M hM) : Between a.rectangle (1 / 64) (7 / 8) := by
  apply phaseRectangle_between (instruction_source_positive M hM a.owner)
    (instruction_target_positive M hM a.owner)
    (instruction_endpoint_bounds M hM a.owner).1 (instruction_endpoint_bounds M hM a.owner).2
    (instruction_halfWidthQ_bound M hM a.owner).1 (instruction_halfWidthQ_bound M hM a.owner).2
    (parkingFor_between M hM a.owner)
  apply endpoints_of_carrier (parkingBox_positive (bandScale_pos M) _)
  intro x hx j
  have h := parkingBox_bounds (bandScale_pos M).le (bandScale_le M) (branchIndex M hM a.owner) hx
  fin_cases j <;> norm_num <;> constructor <;> linarith [h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem compiledPulse_inUnit (M : Alternating.Machine) (hM : M.WellFormed)
    (i : Fin (actions M hM).length) : (compiledPulse M hM i).InUnit := by
  have hδ := routingCollar_parking_bound M hM
  have hε := parkingScale_le (geometricBranches M hM).length
  have hR := Action.rectangle_between ((actions M hM).get i)
  refine ⟨(PlanarTiming.intervals i).1, (PlanarTiming.intervals i).2.2, ?_⟩
  intro j
  have hj := hR j
  change 0 < ((actions M hM).get i).rectangle.lower j - 2 * routingCollar M hM ∧
    ((actions M hM).get i).rectangle.upper j + 2 * routingCollar M hM < 1
  constructor <;> linarith

end ForcedComputation.Recorder.Planar

end OAI
