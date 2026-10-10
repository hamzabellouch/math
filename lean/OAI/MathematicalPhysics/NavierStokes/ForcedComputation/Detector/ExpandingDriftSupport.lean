import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingDrift
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingConcentrationFamily

namespace OAI

/-! Compact horizontal support on every finite time interval follows
from the finite number of stages that have begun. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder Set

private theorem movingGate_compact_family {R : ℝ} (hR : 0 < R)
    {c : ℝ → Plane} {B : ℝ} (hB : ∀ t, ‖c t‖ ≤ B) :
    ∃ K : Set Plane, IsCompact K ∧ ∀ t x, x ∉ K → movingGate R c t x = 0 := by
  let K : Set Plane := Icc (fun _ => -B - 3 * R) (fun _ => B + 3 * R)
  refine ⟨K, isCompact_Icc, ?_⟩
  intro t x hx
  apply translationGate_eq_zero
  intro hz
  have hb := gateCutoff_tsupport hR hz
  apply hx
  constructor <;> intro j
  · have hc : |c t j| ≤ B :=
      (show |c t j| ≤ ‖c t‖ from by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c t) j).trans (hB t)
    have hj := (abs_le.mp (hb j)).1
    have hjc := (abs_le.mp hc).1
    change -B - 3 * R ≤ x j
    change -(3 * R) ≤ x j - c t j at hj
    linarith
  · have hc : |c t j| ≤ B :=
      (show |c t j| ≤ ‖c t‖ from by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c t) j).trans (hB t)
    have hj := (abs_le.mp (hb j)).2
    have hjc := (abs_le.mp hc).2
    change x j ≤ B + 3 * R
    change x j - c t j ≤ 3 * R at hj
    linarith

theorem recorderStageField_compact_family (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (d : ℕ)
    (a : ℝ) {T R R' : ℝ} (hT : 0 < T) (hR : 0 < R) :
    ∃ K : Set Plane, IsCompact K ∧
      ∀ t x, x ∉ K → recorderStageField M hM blank d a T R R' t x = 0 := by
  classical
  have hi (w : StageWire M hM blank d) : ∃ K : Set Plane, IsCompact K ∧
      ∀ t x, x ∉ K → movingGate R (wireCurve M hM blank d a T R R' w) t x = 0 := by
    obtain ⟨B, _, hB⟩ := scheduledCenter_bounded a hT (16 * R) (16 * R')
      w.val.1.number w.val.2.number (haltingControl (finiteMachine M hM) w.val.2.control)
    exact movingGate_compact_family hR hB
  choose K hK hzero using hi
  refine ⟨⋃ w, K w, isCompact_iUnion hK, ?_⟩
  intro t x hx
  apply Finset.sum_eq_zero
  intro w _
  exact hzero w t x (fun hw => hx (mem_iUnion.mpr ⟨w, hw⟩))

theorem expandingDrift_compact_on_finite_intervals (M : Alternating.Machine)
    (hM : M.WellFormed) (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {ν D K : ℝ} (hν : 0 < ν) (hD : 1 ≤ D) (hK : 0 ≤ K) (T : ℝ) :
    ∃ L : Set Plane, IsCompact L ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x, x ∉ L → expandingDrift M hM blank m ν D K t x = 0 := by
  classical
  let N : ℕ := ⌈T + 1⌉₊
  have hi (n : Fin N) : ∃ L : Set Plane, IsCompact L ∧
      ∀ t x, x ∉ L → stageDrift M hM blank m ν D K n.val t x = 0 :=
    recorderStageField_compact_family M hM blank (m + n.val) _
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hν hD hK n.val))
      (radius_pos hν hD hK n.val)
  choose L hL hzero using hi
  refine ⟨⋃ n : Fin N, L n, isCompact_iUnion hL, ?_⟩
  intro t ht x hx
  rw [expandingDrift_eq_prefix M hM blank m hν hD hK T N (Nat.le_ceil _) ht.2]
  apply Finset.sum_eq_zero
  intro n hn
  have hnN : n < N := Finset.mem_range.mp hn
  exact hzero ⟨n, hnN⟩ t x (fun hxn => hx (mem_iUnion.mpr ⟨⟨n, hnN⟩, hxn⟩))

end ForcedComputation.ExpandingDetector

end

end OAI
