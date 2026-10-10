import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.SphereCutoffsAffine

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340.Construction

theorem continuous_cutoff_phase_pow (D : SphereData)
    (hχ : Continuous D.cutoff)
    (hzero : ∀ᶠ z in 𝓝 (((0 : ℂ) : Sphere)), D.cutoff z = 0)
    (hinfty : ∀ᶠ z in 𝓝 (∞ : Sphere), D.cutoff z = 0) (k : ℕ) :
    Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k) := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
      apply (show ContinuousAt (fun _ : Sphere => (0 : ℂ)) _ from
        continuousAt_const).congr_of_eventuallyEq
      filter_upwards [hinfty] with z hz
      simp [hz]
  | coe z =>
      by_cases hz : z = 0
      · subst z
        apply (show ContinuousAt (fun _ : Sphere => (0 : ℂ)) _ from
          continuousAt_const).congr_of_eventuallyEq
        filter_upwards [hzero] with z hz
        simp [hz]
      · rw [OnePoint.continuousAt_coe]
        have hcut : Continuous (fun z : ℂ => (D.cutoff (z : Sphere) : ℂ)) :=
          Complex.continuous_ofReal.comp (hχ.comp OnePoint.continuous_coe)
        have hphase : ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z :=
          continuousAt_id.div
            (Complex.continuous_ofReal.continuousAt.comp continuousAt_id.norm)
            (by simp [hz])
        exact hcut.continuousAt.mul (hphase.pow k)

theorem continuous_prediction (D : SphereData) (he : Continuous D.gate) :
    Continuous (prediction D) := by
  have hb : Continuous Clock.barrier := (Clock.contDiff_barrier (n := 1)).continuous
  have hi : Continuous (fun p : ℝ × Sphere => Clock.increment p.1 (D.gate p.2)) :=
    (hb.comp continuous_fst).add
      ((continuous_const.sub (hb.comp continuous_fst)).mul (he.comp continuous_snd))
  exact (continuous_fst.add hi).prodMk
    (continuous_perturbedSquare.comp (continuous_const.prodMk continuous_snd))

theorem continuous_predictedClock (D : SphereData) (he : Continuous D.gate) (m : ℕ) :
    Continuous (fun p : ℝ × Sphere => predictedClock D m p.1 p.2) :=
  continuous_fst.comp ((continuous_prediction D he).iterate m)

theorem continuous_inputTerm (D : SphereData) (he : Continuous D.gate)
    (hangle : ∀ k : ℕ, Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k))
    (i : Fin 3) (n : ℕ) :
    Continuous (fun p : ℝ × Sphere => inputTerm D i n p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × Sphere =>
      (((D.L⁻¹) ^ n * readoutCoeff i (predictedClock D (n + 1) p.1 p.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.mul
      (((readoutCoeff_contDiff i (n := 1)).continuous).comp
        (continuous_predictedClock D he (n + 1))))
  convert hc.mul ((hangle (2 ^ (n + 2))).comp continuous_snd) using 1
  ext p
  simp only [inputTerm, Complex.ofReal_mul, Pi.mul_apply, Function.comp_apply, mul_assoc]

theorem continuous_baseInput (D : SphereData) (he : Continuous D.gate)
    (hangle : ∀ k : ℕ, Continuous (fun z : Sphere => (D.cutoff z : ℂ) * phase z ^ k))
    (hL : 1 < D.L) (hχ0 : ∀ z, 0 ≤ D.cutoff z) (hχ1 : ∀ z, D.cutoff z ≤ 1)
    (i : Fin 3) : Continuous (fun p : ℝ × Sphere => baseInput D i p.1 p.2) := by
  have hL0 : 0 < D.L := by linarith
  have hgeom : Summable (fun n : ℕ => (D.L⁻¹) ^ n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hL0.le) ((inv_lt_one₀ hL0).2 hL)
  have hs : Continuous (fun p : ℝ × Sphere => ∑' n : ℕ, inputTerm D i n p.1 p.2) :=
    continuous_tsum (continuous_inputTerm D he hangle i) hgeom
      (fun n p => norm_inputTerm_le D hL0.le hχ0 hχ1 i n p.1 p.2)
  exact (Complex.continuous_ofReal.comp
    (((preparationCoeff_contDiff (n := 1)).continuous.comp continuous_fst).div_const 10)).mul hs

theorem preparationCutoff_eventually_zero_at_zero :
    ∀ᶠ z in 𝓝 (((0 : ℂ) : Sphere)), SphereCutoffs.onePointPreparationCutoff z = 0 := by
  rw [OnePoint.nhds_coe_eq]
  change ∀ᶠ z : ℂ in 𝓝 0, SphereCutoffs.onePointPreparationCutoff (z : Sphere) = 0
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 3)] with z hz
  apply SphereCutoffs.affinePreparationCutoff_eq_zero_of_small
  have h : ‖z‖ < 1 / 3 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  exact h.le

theorem preparationCutoff_eventually_zero_at_infty :
    ∀ᶠ z in 𝓝 (∞ : Sphere), SphereCutoffs.onePointPreparationCutoff z = 0 := by
  rw [OnePoint.nhds_infty_eq, Filter.eventually_sup]
  constructor
  · change ∀ᶠ z : ℂ in coclosedCompact ℂ,
      SphereCutoffs.onePointPreparationCutoff (z : Sphere) = 0
    filter_upwards [(isCompact_closedBall (0 : ℂ) 2).compl_mem_coclosedCompact_of_isClosed
      Metric.isClosed_closedBall] with z hz
    apply SphereCutoffs.affinePreparationCutoff_eq_zero_of_large
    have h : 2 < ‖z‖ := by
      simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hz
    nlinarith [sq_nonneg (‖z‖ - 2)]
  · simp

theorem continuous_baseInput_of_standard_cutoffs (D : SphereData)
    (he : D.gate = SphereCutoffs.onePointClockGate)
    (hχ : D.cutoff = SphereCutoffs.onePointPreparationCutoff)
    (hL : 1 < D.L) (i : Fin 3) :
    Continuous (fun p : ℝ × Sphere => baseInput D i p.1 p.2) := by
  apply continuous_baseInput D
  · simpa only [he] using SphereCutoffs.continuous_onePointClockGate
  · intro k
    apply continuous_cutoff_phase_pow D
    · simpa only [hχ] using SphereCutoffs.continuous_onePointPreparationCutoff
    · simpa only [hχ] using preparationCutoff_eventually_zero_at_zero
    · simpa only [hχ] using preparationCutoff_eventually_zero_at_infty
  · exact hL
  · intro z
    simpa only [hχ] using (SphereCutoffs.onePointPreparationCutoff_mem_Icc z).1
  · intro z
    simpa only [hχ] using (SphereCutoffs.onePointPreparationCutoff_mem_Icc z).2

end Problem340.Construction

end

end OAI
