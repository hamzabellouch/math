import OAI.Probability.SLE.Stochastic.PlanarDynkin

namespace OAI

/-! The compact-test planar compensated process has zero mean increments
on every event in the original past, including its stopped finite grids. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarCompensated (f : ℝ×ℝ → ℝ) (t : ℝ≥0) (b : Driver×Driver) : ℝ :=
  f (planarWiener t b)-∫ u in (0:ℝ)..(t:ℝ), planarGenerator f (planarWiener u.toNNReal b)

lemma planar_compensated_integrable
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (t : ℝ≥0) :
    Integrable (planarCompensated f t) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  have hi : Integrable (fun b => f (planarWiener t b)) (W.prod W) := by
    simpa only [Measure.restrict_univ] using planar_compact_eval_integrable W hW f hf hc univ t
  exact hi.sub (bounded_interval_integral_integrable 0 t t.coe_nonneg _
    (planar_generator_joint_measurable f hf) D (fun u b => hD _))

lemma planar_compensated_past_integral_zero
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s t : ℝ≥0) (hst : s ≤ t) (A : Set (Driver×Driver))
    (hA : MeasurableSet[planarWienerFiltration s] A) :
    (∫ b in A, planarCompensated f t b-planarCompensated f s b ∂W.prod W)=0 := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  let G (u : ℝ) (b : Driver×Driver) := planarGenerator f (planarWiener u.toNNReal b)
  have hG : Measurable (Function.uncurry G) := planar_generator_joint_measurable f hf
  have hGb (u b) : |G u b| ≤ D := hD _
  have hGi (a c : ℝ) (h : a ≤ c) (b : Driver×Driver) :=
    bounded_time_section_intervalIntegrable a c h G hG D hGb b
  have hp (b : Driver×Driver) : planarCompensated f t b-planarCompensated f s b =
      (f (planarWiener t b)-f (planarWiener s b))-∫ u in (s:ℝ)..(t:ℝ), G u b := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hGi 0 s s.coe_nonneg b) (hGi s t hst b)
    dsimp only [planarCompensated]
    change _ = _ at h
    linarith
  simp_rw [hp]
  have hfi := (planar_compact_eval_integrable W hW f hf hc A t).sub
    (planar_compact_eval_integrable W hW f hf hc A s)
  have hdi := bounded_interval_integral_integrable (P := (W.prod W).restrict A)
    s t hst G hG D hGb
  have hfi' : Integrable (fun b => f (planarWiener t b)-f (planarWiener s b))
      ((W.prod W).restrict A) := hfi
  rw [integral_sub hfi' hdi,planarWiener_dynkin W hW f hf hc s t hst A hA,sub_self]

lemma planar_compensated_grid_integral
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (τ : Driver×Driver → ℝ≥0)
    (hτ : IsStoppingTime planarWienerFiltration (fun b => (τ b : WithTop ℝ≥0)))
    (T : ℝ≥0) (hb : ∀ b, τ b ≤ T) (n : ℕ) :
    (∫ b, planarCompensated f (stopGrid n (τ b)) b ∂W.prod W)=
      ∫ b, f (planarWiener 0 b) ∂W.prod W := by
  let ℱn := gridFiltration planarWienerFiltration n
  have hbound (b) : stopGridIndex n (τ b) ≤ stopGridIndex n T := by
    exact (stopGridIndex_le n _ _).mpr ((hb b).trans (stopGrid_bounds n T).1)
  have hE (j : ℕ) : MeasurableSet[ℱn j] {b | j<stopGridIndex n (τ b)} := by
    have hle : MeasurableSet[planarWienerFiltration (stopGridTime n j)] {b | τ b ≤ stopGridTime n j} := by
      simpa only [WithTop.coe_le_coe] using hτ (stopGridTime n j)
    have he : {b | j<stopGridIndex n (τ b)}={b | τ b ≤ stopGridTime n j}ᶜ := by
      ext b
      simp only [mem_compl_iff,mem_ofPred_eq,← stopGridIndex_le,not_le]
    rw [he]
    exact hle.compl
  have he := finite_grid_stopped_integral_eq ℱn (fun j => planarCompensated f (stopGridTime n j))
    (fun j => planar_compensated_integrable W hW f hf hc _)
    (fun b => stopGridIndex n (τ b)) (stopGridIndex n T) hbound hE
    (fun j A hA => planar_compensated_past_integral_zero W hW f hf hc _ _
      (monotone_stopGridTime n (Nat.le_succ j)) A hA)
  simpa only [stopGrid,stopGridTime,Nat.cast_zero,zero_div,planarCompensated,
    NNReal.coe_zero,intervalIntegral.integral_same,sub_zero] using he

end SLEExactGauge

end

end OAI
