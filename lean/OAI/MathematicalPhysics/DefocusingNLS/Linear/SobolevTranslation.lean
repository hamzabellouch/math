import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevNonlinearity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchrodingerInteraction

namespace OAI

/-! # Spatial translations on the actual Fourier Sobolev space -/

open Filter Topology
open scoped ENNReal ComplexConjugate

namespace DefocusingNLS

/-- Translation by `x` multiplies the Fourier coefficients by `exp(i n·x)`. -/
noncomputable def sobolevTranslation (x : SchrodingerTorus) : FourierL2 →ₗᵢ[ℂ] FourierL2 where
  toFun f := ⟨fun n => torusCharacter n x * f n, (lp.memℓp f).mono' (by intro n; simp)⟩
  map_add' f g := by ext n; exact mul_add _ _ _
  map_smul' c f := by ext n; simp [mul_left_comm]
  norm_map' f := by
    apply le_antisymm
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simp
    · apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      simp

@[simp] theorem sobolevTranslation_apply (x : SchrodingerTorus) (f : FourierL2)
    (n : frequencyLattice) : sobolevTranslation x f n = torusCharacter n x * f n := rfl

@[simp] theorem sobolevTranslation_zero (f : FourierL2) : sobolevTranslation 0 f = f := by
  ext n
  simp

theorem sobolevTranslation_add (x y : SchrodingerTorus) (f : FourierL2) :
    sobolevTranslation (x + y) f = sobolevTranslation x (sobolevTranslation y f) := by
  ext n
  simp only [sobolevTranslation_apply, torusCharacter_add, mul_assoc]

/-- The Fourier action represents translation of the continuous torus function. -/
theorem sobolevTorusFunction_translation (k : ℝ) (hk : 6 < k)
    (x y : SchrodingerTorus) (f : FourierL2) :
    sobolevTorusFunction k (sobolevTranslation x f) y = sobolevTorusFunction k f (x + y) := by
  simp only [sobolevTorusFunction_eq_tsum k hk]
  apply tsum_congr
  intro n
  simp only [sobolevFourierCoefficient, sobolevTranslation_apply, torusCharacter_add,
    Algebra.smul_def]
  ring

/-- Strong continuity of spatial translation in every represented Sobolev order. -/
theorem continuous_sobolevTranslation (f : FourierL2) :
    Continuous (fun x : SchrodingerTorus => sobolevTranslation x f) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hs : Summable (fun n : frequencyLattice => 4 * ‖f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      ((lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mul_left 4
  have hlim := tendsto_tsum_of_dominated_convergence hs
    (f := fun x n => ‖sobolevTranslation x f n - sobolevTranslation x₀ f n‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (𝓕 := 𝓝 x₀)
    (by
      intro n
      have hc : Continuous (fun x : SchrodingerTorus =>
          ‖sobolevTranslation x f n - sobolevTranslation x₀ f n‖ ^ 2) :=
        ((((torusCharacter n).continuous.fun_mul continuous_const).fun_sub
          continuous_const).norm.fun_pow 2)
      simpa using (hc.continuousAt (x := x₀)).tendsto)
    (Filter.Eventually.of_forall (by
      intro x n
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hn : ‖sobolevTranslation x f n - sobolevTranslation x₀ f n‖ ≤ 2 * ‖f n‖ := by
        calc
          _ ≤ ‖sobolevTranslation x f n‖ + ‖sobolevTranslation x₀ f n‖ := norm_sub_le _ _
          _ = 2 * ‖f n‖ := by simp; ring
      nlinarith [norm_nonneg (sobolevTranslation x f n - sobolevTranslation x₀ f n),
        norm_nonneg (f n)]))
  have hsq : Tendsto (fun x => ‖sobolevTranslation x f - sobolevTranslation x₀ f‖ ^ 2)
      (𝓝 x₀) (𝓝 0) := by
    have heq (x : SchrodingerTorus) := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
      (sobolevTranslation x f - sobolevTranslation x₀ f)
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] at heq
    simpa only [heq, tsum_zero] using hlim
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hn' : Tendsto (fun x => ‖sobolevTranslation x f - sobolevTranslation x₀ f‖)
      (𝓝 x₀) (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

/-- Spatial shifts and initial data vary jointly continuously in the Sobolev norm. -/
theorem continuous_sobolevTranslation_uncurry :
    Continuous (fun p : SchrodingerTorus × FourierL2 => sobolevTranslation p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hu : ∀ᶠ q : SchrodingerTorus × FourierL2 in 𝓝 p, dist q.2 p.2 < ε / 2 :=
    (continuous_snd.continuousAt.tendsto).eventually
      (Metric.ball_mem_nhds p.2 (by linarith))
  have hs : ∀ᶠ q : SchrodingerTorus × FourierL2 in 𝓝 p,
      dist (sobolevTranslation q.1 p.2) (sobolevTranslation p.1 p.2) < ε / 2 :=
    (((continuous_sobolevTranslation p.2).comp continuous_fst).continuousAt.tendsto).eventually
      (Metric.ball_mem_nhds _ (by linarith))
  filter_upwards [hu, hs] with q hqu hqs
  calc
    _ ≤ dist (sobolevTranslation q.1 q.2) (sobolevTranslation q.1 p.2) +
        dist (sobolevTranslation q.1 p.2) (sobolevTranslation p.1 p.2) := dist_triangle _ _ _
    _ = dist q.2 p.2 + dist (sobolevTranslation q.1 p.2) (sobolevTranslation p.1 p.2) := by
      rw [(sobolevTranslation q.1).dist_map]
    _ < ε := by linarith

end DefocusingNLS

end OAI
