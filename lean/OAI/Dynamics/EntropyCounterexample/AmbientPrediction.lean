import OAI.Dynamics.EntropyCounterexample.Clock
import OAI.Dynamics.EntropyCounterexample.SphereCutoffs
import OAI.Dynamics.EntropyCounterexample.SphereDoubling
import OAI.Dynamics.EntropyCounterexample.PredictionDerivative

namespace OAI

noncomputable section

namespace Problem340.AmbientPrediction

abbrev Ambient := ℝ × SphereAmbient

def predictor (x : Ambient) : Ambient :=
  (x.1 + Clock.increment x.1 (SphereCutoffs.clockGateAmbient x.2),
    SphereDoubling.ambientMap x.2)

def cylinder : Set Ambient := Set.univ ×ˢ Metric.sphere (0 : SphereAmbient) 1

@[fun_prop]
theorem contDiff_predictor {n : ℕ∞} : ContDiff ℝ n predictor := by
  exact (contDiff_fst.add (Clock.contDiff_increment contDiff_fst
    (SphereCutoffs.contDiff_clockGateAmbient.comp contDiff_snd))).prodMk
      ((SphereDoubling.contDiff_ambientMap n).comp contDiff_snd)

theorem predictor_equivariant (x : Ambient) :
    predictor (x + (100, 0)) = predictor x + (100, 0) := by
  apply Prod.ext
  · change x.1 + 100 + Clock.increment (x.1 + 100)
      (SphereCutoffs.clockGateAmbient (x.2 + 0)) =
        (x.1 + Clock.increment x.1 (SphereCutoffs.clockGateAmbient x.2)) + 100
    rw [add_zero]
    have hi := Clock.increment_periodic (SphereCutoffs.clockGateAmbient x.2) x.1
    dsimp at hi
    rw [hi]
    ring
  · simp [predictor]

theorem predictor_preserves_cylinder : Set.MapsTo predictor cylinder cylinder := by
  intro x hx
  exact ⟨Set.mem_univ _, SphereDoubling.ambientMap_mem_sphere ⟨x.2, hx.2⟩⟩

def clockPrediction (m : ℕ) (x : Ambient) : ℝ := (predictor^[m] x).1

@[fun_prop]
theorem contDiff_clockPrediction (m : ℕ) {n : ℕ∞} :
    ContDiff ℝ n (clockPrediction m) :=
by
  have hi : ContDiff ℝ n (predictor^[m]) := by
    induction m with
    | zero => simpa using (contDiff_id : ContDiff ℝ n (id : Ambient → Ambient))
    | succ m ih =>
      rw [Function.iterate_succ]
      exact ih.comp contDiff_predictor
  exact hi.fst

theorem exists_derivative_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ cylinder, ‖fderiv ℝ predictor x‖ ≤ B := by
  have hperiod (z : SphereAmbient) :
      Function.Periodic (fun t => fderiv ℝ predictor (t, z)) 100 := by
    intro t
    have heq : fderiv ℝ predictor ((t, z) + (100, 0)) =
        fderiv ℝ predictor (t, z) := by
      calc
        _ = fderiv ℝ (fun y => predictor (y + (100, 0))) (t, z) :=
          (fderiv_comp_add_right (100, 0)).symm
        _ = fderiv ℝ (fun y => predictor y + (100, 0)) (t, z) :=
          congrArg (fun f => fderiv ℝ f (t, z)) (funext predictor_equivariant)
        _ = fderiv ℝ predictor (t, z) := fderiv_add_const (100, 0)
    simpa using heq
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.prod (isCompact_sphere (0 : SphereAmbient) 1)).exists_bound_of_continuousOn
      ((contDiff_predictor (n := 1)).continuous_fderiv one_ne_zero).continuousOn
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨r, hr, heq⟩ := (hperiod x.2).exists_mem_Ico₀
    (by norm_num : (0 : ℝ) < 100) x.1
  rw [show fderiv ℝ predictor x = fderiv ℝ predictor (r, x.2) from heq]
  exact (hC (r, x.2) ⟨⟨hr.1, hr.2.le⟩, hx.2⟩).trans (le_max_right _ _)

theorem exists_clockPrediction_derivative_bound :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ m x, x ∈ cylinder →
      ‖fderiv ℝ (clockPrediction m) x‖ ≤ B ^ m := by
  obtain ⟨B, hB, hbound⟩ := exists_derivative_bound
  refine ⟨B, hB, ?_⟩
  intro m x hx
  exact Prediction.norm_fderiv_projection_iterate_le_on
    (fun y _ => (contDiff_predictor (n := 1)).differentiable one_ne_zero y)
    predictor_preserves_cylinder (by linarith) hbound
    (ContinuousLinearMap.fst ℝ ℝ SphereAmbient)
    (ContinuousLinearMap.norm_fst_le ℝ ℝ SphereAmbient) m x hx

theorem exists_gain :
    ∃ L B : ℝ, 2 < L ∧ 1 ≤ B ∧ B < L ∧ ∀ m x, x ∈ cylinder →
      ‖fderiv ℝ (clockPrediction m) x‖ ≤ B ^ m := by
  obtain ⟨B, hB, hbound⟩ := exists_clockPrediction_derivative_bound
  exact ⟨B + 3, B, by linarith, hB, by linarith, hbound⟩

theorem norm_fderiv_clockPrediction_chart_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : E → Ambient} {x : E} {B C : ℝ}
    (hB : 0 ≤ B)
    (hbound : ∀ m y, y ∈ cylinder → ‖fderiv ℝ (clockPrediction m) y‖ ≤ B ^ m)
    (hκ : DifferentiableAt ℝ κ x) (hx : κ x ∈ cylinder)
    (hC : ‖fderiv ℝ κ x‖ ≤ C) (m : ℕ) :
    ‖fderiv ℝ ((clockPrediction m) ∘ κ) x‖ ≤ B ^ m * C := by
  rw [fderiv_comp x ((contDiff_clockPrediction m (n := 1)).differentiable
    one_ne_zero (κ x)) hκ]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul (hbound m (κ x) hx) hC (norm_nonneg _) (pow_nonneg hB m))

end Problem340.AmbientPrediction

end

end OAI
