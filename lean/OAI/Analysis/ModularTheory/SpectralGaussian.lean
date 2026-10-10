import OAI.Analysis.ModularTheory.GaussianRegularizers
import OAI.Analysis.ModularRecovery.StrongLimits
import OAI.Analysis.ModularTheory.HalfGraphCutoff

namespace OAI

/-! Strong Gaussian cutoffs in the modular spectral calculus. The compact
spectral estimate is quantitative; no boundedness assumption on the modular
generator is introduced. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace WeakPureInfiniteness

lemma modularGaussian_error (n : ℕ) (t : ℝ) :
    ‖modularGaussian n t - 1‖ ≤ t ^ 2 / (n + 1 : ℝ) := by
  have hx : 0 ≤ t ^ 2 / (n + 1 : ℝ) := div_nonneg (sq_nonneg _) (by positivity)
  have he : Real.exp (-t ^ 2 / (n + 1 : ℝ)) ≤ 1 := by
    rw [neg_div]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)
  have hl := Real.add_one_le_exp (-(t ^ 2 / (n + 1 : ℝ)))
  rw [neg_div] at he
  rw [modularGaussian_apply, neg_div, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr he)]
  linarith

lemma modularGaussian_compact_error (χ : BoundedContinuousFunction ℝ ℂ)
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖modularGaussian n * χ - χ‖ ≤ C / (n + 1 : ℝ) := by
  obtain ⟨R, hR, hRs⟩ := hχ.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R ^ 2 * ‖χ‖, mul_nonneg (sq_nonneg _) (norm_nonneg _), fun n => ?_⟩
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro t
  change ‖modularGaussian n t * χ t - χ t‖ ≤ _
  by_cases ht : t ∈ tsupport (χ : ℝ → ℂ)
  · rw [← sub_one_mul, norm_mul]
    have hb : t ^ 2 ≤ R ^ 2 := by
      have h := hRs t ht
      rw [Real.norm_eq_abs] at h
      have hh : |t| ^ 2 ≤ R ^ 2 := by gcongr
      simpa only [sq_abs] using hh
    calc
      _ ≤ (t ^ 2 / (n + 1 : ℝ)) * ‖χ t‖ :=
        mul_le_mul_of_nonneg_right (modularGaussian_error n t) (norm_nonneg _)
      _ ≤ (R ^ 2 / (n + 1 : ℝ)) * ‖χ‖ := by
        gcongr
        exact χ.norm_coe_le_norm t
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport ht, mul_zero, sub_self, norm_zero]
    positivity

lemma modularGaussian_compact_tendsto (χ : BoundedContinuousFunction ℝ ℂ)
    (hχ : HasCompactSupport (χ : ℝ → ℂ)) :
    Tendsto (fun n => modularGaussian n * χ) atTop (𝓝 χ) := by
  obtain ⟨C, hC, hb⟩ := modularGaussian_compact_error χ hχ
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) hb
  have h := (tendsto_const_div_atTop_nhds_zero_nat C).comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

/-- A bounded regularization of the half-exponential. -/
def modularHalfGaussian (n : ℕ) : BoundedContinuousFunction ℝ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t : ℝ => (Real.exp (-t ^ 2 / (n + 1) + t / 2) : ℂ)) (by fun_prop)
    (Real.exp ((n + 1 : ℝ) / 16)) (by
      intro t
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hp : (0 : ℝ) < n + 1 := by positivity
      have he : (-t ^ 2 / (n + 1 : ℝ)) * (n + 1 : ℝ) = -t ^ 2 :=
        div_mul_cancel₀ _ hp.ne'
      nlinarith [sq_nonneg (4 * t - (n + 1 : ℝ))])

@[simp] lemma modularHalfGaussian_apply (n : ℕ) (t : ℝ) :
    modularHalfGaussian n t = (Real.exp (-t ^ 2 / (n + 1) + t / 2) : ℂ) := rfl

lemma modularHalfGaussian_resolvent (n : ℕ) :
    modularHalfGaussian n * BoundedRecovery.halfResolvent =
      modularGaussian n * (1 - BoundedRecovery.halfResolvent) := by
  ext t
  change (Real.exp (-t ^ 2 / (n + 1) + t / 2) : ℂ) *
    BoundedRecovery.halfResolvent t =
      (Real.exp (-t ^ 2 / (n + 1)) : ℂ) * (1 - BoundedRecovery.halfResolvent t)
  rw [Real.exp_add, Complex.ofReal_mul, mul_assoc]
  congr 1
  rw [BoundedRecovery.halfResolvent_apply]
  have hp := Real.exp_pos (t / 2)
  have h : Real.exp (t / 2) * (Real.exp (t / 2) + 1)⁻¹ =
      1 - (Real.exp (t / 2) + 1)⁻¹ := by
    field_simp
    ring
  exact_mod_cast h

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma modularGaussian_calculus_strong (D : BoundedRecovery.RealSpectralCalculus H) (v : H) :
    Tendsto (fun n => D.calculus (modularGaussian n) v) atTop (𝓝 v) := by
  have h := D.tendsto_calculus_of_compact modularGaussian 1 zero_le_one
    (fun n => (BoundedContinuousFunction.norm_le zero_le_one).mpr (modularGaussian_norm_le n))
    (fun χ hχ => by simpa only [one_mul] using modularGaussian_compact_tendsto χ hχ) v
  simpa only [map_one, one_apply_eq_self] using h

lemma modularHalfGaussian_halfGraph (D : BoundedRecovery.RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) (n : ℕ) :
    D.calculus (modularHalfGaussian n) x = D.calculus (modularGaussian n) y :=
  (D.halfGraph_multiplier hxy (modularGaussian n) (modularHalfGaussian n)
    (modularHalfGaussian_resolvent n)).symm

lemma modularHalfGaussian_calculus_strong (D : BoundedRecovery.RealSpectralCalculus H)
    {x y : H} (hxy : (x, y) ∈ D.halfGraph) :
    Tendsto (fun n => D.calculus (modularHalfGaussian n) x) atTop (𝓝 y) := by
  simpa only [modularHalfGaussian_halfGraph D hxy] using modularGaussian_calculus_strong D y

lemma modularHalfGaussian_tomita (S : BoundedRecovery.StandardModularData H)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    Tendsto (fun n => S.D.calculus (modularHalfGaussian n) (star a S.xi)) atTop
      (𝓝 (S.J (a S.xi))) := by
  have h := S.core_halfGraph (star a) (star_mem ha)
  simp only [star_star] at h
  exact modularHalfGaussian_calculus_strong S.D h

lemma modularHalfGaussian_tomita_norm (S : BoundedRecovery.StandardModularData H)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) :
    Tendsto (fun n => ‖S.D.calculus (modularHalfGaussian n) (star a S.xi)‖) atTop
      (𝓝 ‖a S.xi‖) := by
  simpa only [S.J.norm_map] using (modularHalfGaussian_tomita S a ha).norm

end WeakPureInfiniteness

end

end OAI
