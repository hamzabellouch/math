import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingAmplitude
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingCenterVelocity
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingStageTimes

namespace OAI

/-! Actual scheduled wire centers satisfy the geometric amplitude budget.
The spatial radius cancels against the chosen stage duration. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder
open scoped ContDiff

theorem wire_address_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m n : ℕ)
    (w : StageWire M hM blank (m+n)) :
    (w.val.1.number : ℝ) ≤ (addressFactor M blank m : ℝ)*(addressGrowth M blank : ℝ)^(n+1) ∧
    (w.val.2.number : ℝ) ≤ (addressFactor M blank m : ℝ)*(addressGrowth M blank : ℝ)^(n+1) := by
  constructor
  · apply (address_number_growth_real M blank m n w.val.1).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [pow_succ]
    exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast addressGrowth_ge_one M blank)
  · simpa only [Nat.add_assoc] using address_number_growth_real M blank m (n+1) w.val.2

theorem wireCurve_positive_jet_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ : ℝ} (hσ : 0 < σ) {C : ℝ} (hC0 : 0 ≤ C) (L : ℕ)
    (hC : ∀ q ≤ L, ∀ t, |iteratedDeriv q (smoothRamp 0 1) t| ≤ C)
    (n : ℕ) (w : StageWire M hM blank (m+n)) (q : ℕ) (hq : 1 ≤ q) (hqL : q ≤ L)
    (t : ℝ) :
    ‖iteratedDeriv q
      (wireCurve M hM blank (m+n)
        (stageStart σ (workGrowth M blank) (workFactor M blank m) n)
        (duration σ (workGrowth M blank) (workFactor M blank m) n)
        (radius σ (workGrowth M blank) (workFactor M blank m) n)
        (radius σ (workGrowth M blank) (workFactor M blank m) (n+1)) w) t‖ ≤
      (4 * (6 : ℝ)^L * C) * stageAmplitude M blank m n := by
  let D := workGrowth M blank
  let K := workFactor M blank m
  let R := radius σ D K n
  let R' := radius σ D K (n+1)
  let T := duration σ D K n
  let B := (addressFactor M blank m : ℝ)*(addressGrowth M blank : ℝ)^(n+1)
  have hD : 1 ≤ D := workGrowth_ge_one M blank
  have hK : 0 ≤ K := workFactor_nonneg M blank m
  have hR := radius_pos hσ hD hK n
  have hR' := radius_pos hσ hD hK (n+1)
  have hRR := radius_grows hσ hD hK n
  have hT : 1 ≤ T := le_trans (by norm_num) (duration_ge_two hσ hD hK n)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hw := wire_address_bounds M hM blank m n w
  have hq0 : 0 ≤ (4 * (6 : ℝ)^L * C) * stageAmplitude M blank m n :=
    mul_nonneg (by positivity) (stageAmplitude_nonneg M blank m n)
  apply iteratedDeriv_plane_bound (wireCurve_smooth M hM blank (m+n) _ _ _ _ w) q t hq0
  intro j
  have hb := scheduledCenter_coordinate_jet_bound hC0 hC (by positivity : 0 ≤ 16*R)
    (by dsimp [R,R'] at *; linarith : 16*R ≤ 16*R') hB hT hq hqL
    (stageStart σ D K n) w.val.1.number w.val.2.number hw.1 hw.2
    (haltingControl (finiteMachine M hM) w.val.2.control) j t
  change |iteratedDeriv q (fun s => scheduledCenter _ T (16*R) (16*R') _ _ _ s j) t| ≤ _
  apply hb.trans_eq
  have hQ : K * D^(n+1)+2 ≠ 0 := by have := (show 0 ≤ K*D^(n+1) by positivity); linarith
  change (4 * (16 * R') * (B + 2)) * ((6 : ℝ)^L / T * C) =
    (4 * (6 : ℝ)^L * C) * ((B+2) / (K * D^(n+1)+2))
  have hTeq : T = 16 * R' * (K * D^(n+1)+2) := rfl
  have hRp : R' ≠ 0 := hR'.ne'
  rw [hTeq]
  field_simp [hRp, hQ]

end ForcedComputation.ExpandingDetector

end

end OAI
