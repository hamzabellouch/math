import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingWireRates
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingNormalizedCenter
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingSeriesBounds

namespace OAI

/-! Uniform bounds for the complete expanding-array drift. The velocity
of each gate pays for the growing finite address table at every stage. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder
open scoped ContDiff BigOperators

private theorem finite_jet_sum_bound {ι : Type*} [Fintype ι]
    (f : ι → (ℝ × Plane) → Plane) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (k : ℕ) (y : ℝ × Plane) (A : ℝ)
    (hA : ∀ i, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (fun x => ∑ i, f i x) y‖ ≤ (Fintype.card ι : ℝ) * A := by
  classical
  rw [iteratedFDeriv_fun_sum_apply (f := f) (fun i _ =>
    ((hf i).of_le (by simp)).contDiffAt)]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : ι, A := Finset.sum_le_sum (fun i _ => hA i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem stage_gate_jet_bound (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (k : ℕ) {C A : ℝ} (hC1 : 1 ≤ C)
    (hC : ∀ i ≤ k+1, ∀ t, |iteratedDeriv i (smoothRamp 0 1) t| ≤ C)
    (hA : 0 ≤ A)
    (hkernel : ∀ j : Fin 2, ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (gateKernel j) x‖ ≤ A)
    (n : ℕ) (w : StageWire M hM blank (m+n)) (y : ℝ × Plane) :
    let D := workGrowth M blank
    let K := workFactor M blank m
    let V := 4 * (6 : ℝ)^(k+1) * C
    let Z := 1+V
    let B := 2 * ∑ i ∈ Finset.range (k+1),
      (k.choose i : ℝ)*V*((k-i).factorial*A*Z^(k-i))
    ‖iteratedFDeriv ℝ k (Function.uncurry (movingGate (radius σ D K n)
      (wireCurve M hM blank (m+n) (stageStart σ D K n) (duration σ D K n)
        (radius σ D K n) (radius σ D K (n+1)) w))) y‖ ≤
      B * stageAmplitude M blank m n := by
  dsimp only
  let D := workGrowth M blank
  let K := workFactor M blank m
  have hD : 1 ≤ D := workGrowth_ge_one M blank
  have hK : 0 ≤ K := workFactor_nonneg M blank m
  let V := 4 * (6 : ℝ)^(k+1) * C
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let Z := 1+V
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let B := 2 * ∑ i ∈ Finset.range (k+1),
    (k.choose i : ℝ)*V*((k-i).factorial*A*Z^(k-i))
  let c := wireCurve M hM blank (m+n) (stageStart σ D K n) (duration σ D K n)
    (radius σ D K n) (radius σ D K (n+1)) w
  have hc : ContDiff ℝ ∞ c := wireCurve_smooth M hM blank (m+n) _ _ _ _ w
  have hvc : ContDiff ℝ ∞ (fun p : ℝ × Plane => deriv c p.1) :=
    ((contDiff_infty_iff_deriv.mp hc).2).comp contDiff_fst
  have hcenter (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDeriv ℝ i (normalizedCenter (radius σ D K n) c) y‖ ≤ Z^i := by
    apply normalizedCenter_positive_jet (radius_ge_one hσ hD hK n) hV hc i hi
    apply (wireCurve_positive_jet_bound M hM blank m hσ (by linarith : 0 ≤ C)
      (k+1) hC n w i hi (by omega) y.1).trans
    exact (mul_le_mul_of_nonneg_left (stageAmplitude_le_one M blank m n) hV).trans_eq
      (mul_one V)
  have hvel (j : Fin 2) (i : ℕ) (hik : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun p : ℝ × Plane => deriv c p.1 j) y‖ ≤
        V*stageAmplitude M blank m n := by
    have hs : ContDiff ℝ ∞ (fun s => deriv c s j) :=
      (contDiff_apply ℝ ℝ j).comp ((contDiff_infty_iff_deriv.mp hc).2)
    apply (time_comp_jet_bound hs i y).trans
    rw [Real.norm_eq_abs, iteratedDeriv_velocity_component hc,
      iteratedDeriv_component hc]
    apply (show |iteratedDeriv (i+1) c y.1 j| ≤ ‖iteratedDeriv (i+1) c y.1‖ from by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (iteratedDeriv (i+1) c y.1) j).trans
    exact wireCurve_positive_jet_bound M hM blank m hσ (by linarith : 0 ≤ C)
      (k+1) hC n w (i+1) (by omega) (by omega) y.1
  rw [movingGate_eq_packet (radius_pos hσ hD hK n).ne']
  apply (gatePacket_jet_bound hvc (normalizedCenter_smooth _ hc) k y hA hZ
    (mul_nonneg hV (stageAmplitude_nonneg M blank m n)) hkernel hvel hcenter).trans_eq
  have he : (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*(V*stageAmplitude M blank m n)*
      ((k-i).factorial*A*Z^(k-i))) =
      (∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*V*((k-i).factorial*A*Z^(k-i))) *
        stageAmplitude M blank m n := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he]
  ring

theorem expandingDrift_all_jets_bounded (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ × Plane,
      ‖iteratedFDeriv ℝ k (Function.uncurry (expandingDrift M hM blank m σ
        (workGrowth M blank) (workFactor M blank m))) y‖ ≤ B := by
  let D := workGrowth M blank
  let K := workFactor M blank m
  have hD : 1 ≤ D := workGrowth_ge_one M blank
  have hK : 0 ≤ K := workFactor_nonneg M blank m
  obtain ⟨C, hC1, hC⟩ := unitRamp_jet_bound (k+1)
  obtain ⟨A, hA, hkernel⟩ := gateKernel_jet_bound k
  let V := 4 * (6 : ℝ)^(k+1) * C
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let Z := 1+V
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  let B := 2 * ∑ i ∈ Finset.range (k+1),
    (k.choose i : ℝ)*V*((k-i).factorial*A*Z^(k-i))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgate (n : ℕ) (w : StageWire M hM blank (m+n)) (y : ℝ × Plane) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (movingGate (radius σ D K n)
        (wireCurve M hM blank (m+n) (stageStart σ D K n) (duration σ D K n)
          (radius σ D K n) (radius σ D K (n+1)) w))) y‖ ≤
        B * stageAmplitude M blank m n := by
    exact stage_gate_jet_bound M hM blank m hσ k hC1 hC hA hkernel n w y
  have hstage (n : ℕ) (y : ℝ × Plane) :
      ‖iteratedFDeriv ℝ k (Function.uncurry (stageDrift M hM blank m σ D K n)) y‖ ≤
        B*(1/2 : ℝ)^n := by
    change ‖iteratedFDeriv ℝ k (fun p : ℝ × Plane =>
      ∑ w : StageWire M hM blank (m+n), movingGate (radius σ D K n)
        (wireCurve M hM blank (m+n) (stageStart σ D K n) (duration σ D K n)
          (radius σ D K n) (radius σ D K (n+1)) w) p.1 p.2) y‖ ≤ _
    have hb := finite_jet_sum_bound
      (fun w : StageWire M hM blank (m+n) =>
        Function.uncurry (movingGate (radius σ D K n)
          (wireCurve M hM blank (m+n) (stageStart σ D K n) (duration σ D K n)
            (radius σ D K n) (radius σ D K (n+1)) w)))
      (fun w => movingGate_smooth _ (wireCurve_smooth M hM blank (m+n) _ _ _ _ w))
      k y (B * stageAmplitude M blank m n) (fun w => hgate n w y)
    apply hb.trans
    calc
      (Fintype.card (StageWire M hM blank (m+n)) : ℝ) * (B * stageAmplitude M blank m n) =
          B * ((Fintype.card (StageWire M hM blank (m+n)) : ℝ) * stageAmplitude M blank m n) := by ring
      _ ≤ B*(1/2 : ℝ)^n := mul_le_mul_of_nonneg_left
        (stageAmplitude_total_bound M hM blank m n) hB
  exact ⟨2*B, by positivity, expandingDrift_jet_bound M hM blank m hσ hD hK k hB hstage⟩

end ForcedComputation.ExpandingDetector

end

end OAI
