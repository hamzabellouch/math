import OAI.Geometry.EinsteinFour.HVarianceApproximation

namespace OAI

/-! Dominated smooth approximation of both Weyl norms and their difference.
The gradient limit uses the actual zero-set support property. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped Topology ContDiff

noncomputable section

theorem contDiff_hRegularizedArgument (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun b : ℝ => hRegularizedArgument b ε) := by
  have hp : ContDiff ℝ ∞ (fun b : ℝ => b ^ 2 + ε ^ 2) := by fun_prop
  exact hp.sqrt (fun b => ne_of_gt (by nlinarith [sq_nonneg b, sq_pos_of_pos hε]))

theorem contDiff_hRegularizedValue (ε : ℝ) (hε : 0 < ε) :
    ContDiff ℝ ∞ (fun b : ℝ => hRegularizedValue b ε) := by
  have hr := contDiff_hRegularizedArgument ε hε
  have hs := hr.sqrt (fun b => ne_of_gt (hRegularizedArgument_pos b ε hε))
  unfold hRegularizedValue MomentObstruction.H
  exact hs.mul ((contDiff_const.add ((hr.pow 2).div_const 40)).sub ((hr.pow 4).div_const 1152))

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def regularizedRadialVector (b ε : ℝ) (p : F) : F :=
  (b / hRegularizedArgument b ε) • p

def regularizedNormEnergy (b ε K : ℝ) (p : F) : ℝ :=
  ‖regularizedRadialVector b ε p‖ ^ 2 / K

def regularizedDifferenceValue (v b ε : ℝ) : ℝ :=
  hRegularizedArgument v ε - hRegularizedArgument b ε

def regularizedDifferenceEnergy (v b ε K : ℝ) (p q : F) : ℝ :=
  ‖regularizedRadialVector v ε p - regularizedRadialVector b ε q‖ ^ 2 / K

theorem regularizedRadialVector_norm_le {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (p : F) :
    ‖regularizedRadialVector b ε p‖ ≤ ‖p‖ := by
  have hr := hRegularizedArgument_pos b ε hε
  have hc0 : 0 ≤ b / hRegularizedArgument b ε := div_nonneg hb hr.le
  have hc1 : b / hRegularizedArgument b ε ≤ 1 :=
    (div_le_one hr).2 (le_hRegularizedArgument b ε hb)
  rw [regularizedRadialVector, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
  exact mul_le_of_le_one_left (norm_nonneg p) hc1

theorem regularizedDifference_square_le {v b ε : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hε : 0 < ε) (p q : F) :
    ‖regularizedRadialVector v ε p - regularizedRadialVector b ε q‖ ^ 2 ≤
      2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hn := (norm_sub_le (regularizedRadialVector v ε p)
    (regularizedRadialVector b ε q)).trans
    (add_le_add (regularizedRadialVector_norm_le hv hε p)
      (regularizedRadialVector_norm_le hb hε q))
  have hs := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg p) (norm_nonneg q))).2 hn
  nlinarith [sq_nonneg (‖p‖ - ‖q‖)]

theorem regularizedDifferenceEnergy_nonneg {v b ε K : ℝ} (hK : 0 ≤ K) (p q : F) :
    0 ≤ regularizedDifferenceEnergy v b ε K p q := div_nonneg (sq_nonneg _) hK

theorem regularizedDifferenceEnergy_le {v b ε K : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hε : 0 < ε) (hK : 1 ≤ K) (p q : F) :
    regularizedDifferenceEnergy v b ε K p q ≤ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  unfold regularizedDifferenceEnergy
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hK)).2
  have hs := regularizedDifference_square_le hv hb hε p q
  have hm := mul_le_mul_of_nonneg_left hK
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖q‖)))
  nlinarith

omit [NormedSpace ℝ F] in
theorem normDifferenceEnergy_le {K : ℝ} (hK : 1 ≤ K) (p q : F) :
    ‖p - q‖ ^ 2 / K ≤ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
  have hsq := (sq_le_sq₀ (norm_nonneg (p - q))
    (add_nonneg (norm_nonneg p) (norm_nonneg q))).2 (norm_sub_le p q)
  have hs : ‖p - q‖ ^ 2 ≤ 2 * (‖p‖ ^ 2 + ‖q‖ ^ 2) := by
    nlinarith [sq_nonneg (‖p‖ - ‖q‖)]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hK)).2
  have hm := mul_le_mul_of_nonneg_left hK
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖q‖)))
  nlinarith

theorem tendsto_regularizedRadialVector (b : ℝ) (p : F) (hb : 0 ≤ b)
    (hz : b = 0 → p = 0) :
    Tendsto (fun ε => regularizedRadialVector b ε p) (𝓝 0) (𝓝 p) := by
  by_cases hzero : b = 0
  · subst b
    rw [hz rfl]
    simp [regularizedRadialVector]
  have h : Tendsto (fun ε => (b / hRegularizedArgument b ε) • p) (𝓝 0)
      (𝓝 ((b / b) • p)) :=
    (tendsto_const_nhds.div (tendsto_hRegularizedArgument b hb) hzero).smul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => p) (𝓝 0) (𝓝 p))
  simpa only [regularizedRadialVector, div_self hzero, one_smul] using h

theorem tendsto_regularizedDifferenceValue (v b : ℝ) (hv : 0 ≤ v) (hb : 0 ≤ b) :
    Tendsto (regularizedDifferenceValue v b) (𝓝 0) (𝓝 (v - b)) :=
  (tendsto_hRegularizedArgument v hv).sub (tendsto_hRegularizedArgument b hb)

theorem tendsto_regularizedDifferenceEnergy (v b K : ℝ) (p q : F)
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
    Tendsto (fun ε => regularizedDifferenceEnergy v b ε K p q) (𝓝 0)
      (𝓝 (‖p - q‖ ^ 2 / K)) :=
  (((tendsto_regularizedRadialVector v p hv hp).sub
    (tendsto_regularizedRadialVector b q hb hq)).norm.pow 2).div_const K

theorem regularizedNormEnergy_eq_difference (b ε K : ℝ) (p : F) :
    regularizedNormEnergy b ε K p = regularizedDifferenceEnergy b 0 ε K p 0 := by
  simp [regularizedNormEnergy, regularizedDifferenceEnergy, regularizedRadialVector]

theorem regularizedDifferenceValue_abs_le {v b ε : ℝ}
    (hv : v ∈ Set.Icc (0 : ℝ) 2) (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) : |regularizedDifferenceValue v b ε| ≤ 6 := by
  have hv3 := hRegularizedArgument_le_three v ε hv ⟨hε.1.le, hε.2⟩
  have hb3 := hRegularizedArgument_le_three b ε hb ⟨hε.1.le, hε.2⟩
  unfold regularizedDifferenceValue
  have hn := abs_sub (hRegularizedArgument v ε) (hRegularizedArgument b ε)
  rw [abs_of_pos (hRegularizedArgument_pos v ε hε.1),
    abs_of_pos (hRegularizedArgument_pos b ε hε.1)] at hn
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aestronglyMeasurable_regularizedRadialVector {b : Ω → ℝ} {p : Ω → F}
    (hb : AEMeasurable b μ) (hp : AEStronglyMeasurable p μ) (ε : ℝ) :
    AEStronglyMeasurable (fun x => regularizedRadialVector (b x) ε (p x)) μ :=
  (hb.div (aemeasurable_hRegularizedArgument hb ε)).aestronglyMeasurable.smul hp

omit [NormedSpace ℝ F] in
theorem integrable_normDifferenceEnergy {K : Ω → ℝ} {p q : Ω → F}
    (hK : AEMeasurable K μ) (hp : AEStronglyMeasurable p μ) (hq : AEStronglyMeasurable q μ)
    (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ) (hq2 : Integrable (fun x => ‖q x‖ ^ 2) μ) :
    Integrable (fun x => ‖p x - q x‖ ^ 2 / K x) μ := by
  have hm : AEStronglyMeasurable (fun x => ‖p x - q x‖ ^ 2 / K x) μ :=
    (((hp.sub hq).norm.pow 2).aemeasurable.div hK).aestronglyMeasurable
  apply ((hp2.add hq2).const_mul 2).mono' hm
  filter_upwards [hK1] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
  exact normDifferenceEnergy_le hx (p x) (q x)

theorem integral_regularizedDifferenceEnergy_tendsto {v b K : Ω → ℝ} {p q : Ω → F}
    (hv : AEMeasurable v μ) (hb : AEMeasurable b μ) (hK : AEMeasurable K μ)
    (hp : AEStronglyMeasurable p μ) (hq : AEStronglyMeasurable q μ)
    (hv0 : ∀ᵐ x ∂μ, 0 ≤ v x) (hb0 : ∀ᵐ x ∂μ, 0 ≤ b x)
    (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hq0 : ∀ᵐ x ∂μ, b x = 0 → q x = 0)
    (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ) (hq2 : Integrable (fun x => ‖q x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedDifferenceEnergy (v x) (b x) (ε n) (K x) (p x) (q x) ∂μ)
      atTop (𝓝 (∫ x, ‖p x - q x‖ ^ 2 / K x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => 2 * (‖p x‖ ^ 2 + ‖q x‖ ^ 2))
  · intro n
    exact ((((aestronglyMeasurable_regularizedRadialVector hv hp (ε n)).sub
      (aestronglyMeasurable_regularizedRadialVector hb hq (ε n))).norm.pow 2).aemeasurable.div
        hK).aestronglyMeasurable
  · exact (hp2.add hq2).const_mul 2
  · intro n
    filter_upwards [hv0, hb0, hK1] with x hvx hbx hKx
    rw [Real.norm_eq_abs, abs_of_nonneg (regularizedDifferenceEnergy_nonneg (by linarith) _ _)]
    exact regularizedDifferenceEnergy_le hvx hbx (hε n) hKx (p x) (q x)
  · filter_upwards [hv0, hb0, hp0, hq0] with x hvx hbx hpx hqx
    exact (tendsto_regularizedDifferenceEnergy (v x) (b x) (K x) (p x) (q x)
      hvx hbx hpx hqx).comp hlim

theorem integral_regularizedNormEnergy_tendsto {v K : Ω → ℝ} {p : Ω → F}
    (hv : AEMeasurable v μ) (hK : AEMeasurable K μ) (hp : AEStronglyMeasurable p μ)
    (hv0 : ∀ᵐ x ∂μ, 0 ≤ v x) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, regularizedNormEnergy (v x) (ε n) (K x) (p x) ∂μ)
      atTop (𝓝 (∫ x, ‖p x‖ ^ 2 / K x ∂μ)) := by
  have h := integral_regularizedDifferenceEnergy_tendsto
    (v := v) (b := fun _ => (0 : ℝ)) (K := K) (p := p) (q := fun _ => (0 : F))
    hv aemeasurable_const hK hp aestronglyMeasurable_const hv0
    (Filter.Eventually.of_forall (fun _ => le_rfl)) hK1 hp0
    (Filter.Eventually.of_forall (fun _ _ => rfl)) hp2
    (by simp) ε hε hlim
  simpa only [← regularizedNormEnergy_eq_difference, sub_zero] using h

theorem integral_regularizedNorm_pow_tendsto [IsFiniteMeasure μ] {v : Ω → ℝ}
    (hv : AEMeasurable v μ) (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => ∫ x, hRegularizedArgument (v x) (ε n) ^ k ∂μ) atTop
      (𝓝 (∫ x, v x ^ k ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (3 : ℝ) ^ k)
  · intro n
    exact ((aemeasurable_hRegularizedArgument hv (ε n)).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hv2] with x hx
    rw [Real.norm_eq_abs, abs_pow, abs_of_pos (hRegularizedArgument_pos _ _ (hε n).1)]
    exact pow_le_pow_left₀ (hRegularizedArgument_pos _ _ (hε n).1).le
      (hRegularizedArgument_le_three _ _ hx ⟨(hε n).1.le, (hε n).2⟩) k
  · filter_upwards [hv2] with x hx
    exact ((tendsto_hRegularizedArgument (v x) hx.1).comp hlim).pow k

theorem integral_regularizedDifferenceValue_pow_tendsto [IsFiniteMeasure μ] {v b : Ω → ℝ}
    (hv : AEMeasurable v μ) (hb : AEMeasurable b μ)
    (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2)
    (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => ∫ x, regularizedDifferenceValue (v x) (b x) (ε n) ^ k ∂μ) atTop
      (𝓝 (∫ x, (v x - b x) ^ k ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (6 : ℝ) ^ k)
  · intro n
    exact (((aemeasurable_hRegularizedArgument hv (ε n)).sub
      (aemeasurable_hRegularizedArgument hb (ε n))).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hv2, hb2] with x hvx hbx
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (regularizedDifferenceValue_abs_le hvx hbx (hε n)) k
  · filter_upwards [hv2, hb2] with x hvx hbx
    exact ((tendsto_regularizedDifferenceValue (v x) (b x) hvx.1 hbx.1).comp hlim).pow k

/-- Difference-of-moments variance depends only on the almost-everywhere class. -/
theorem variance_congr_ae {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 =
      (∫ x, g x ^ 2 ∂μ) - (∫ x, g x ∂μ) ^ 2 := by
  have h1 := integral_congr_ae hfg
  have h2 := integral_congr_ae (hfg.mono (fun _ hx => congrArg (fun z : ℝ => z ^ 2) hx))
  rw [h1, h2]

/-- For probability measure, the centered-square and difference-of-moments
forms agree under precisely the first and second moment integrability. -/
theorem integral_centered_square [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ) =
      (∫ x, f x ^ 2 ∂μ) - (∫ x, f x ∂μ) ^ 2 := by
  have hpoly (x : Ω) : (f x - ∫ y, f y ∂μ) ^ 2 =
      f x ^ 2 - (2 * ∫ y, f y ∂μ) * f x + (∫ y, f y ∂μ) ^ 2 := by ring
  have hadd := integral_add (hf2.sub (hf.const_mul (2 * ∫ y, f y ∂μ)))
    (integrable_const ((∫ y, f y ∂μ) ^ 2))
  have hsub := integral_sub hf2 (hf.const_mul (2 * ∫ y, f y ∂μ))
  simp only [Pi.sub_apply] at hadd hsub
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoly), hadd, hsub, integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]
  ring

/-- The weighted variance for the difference of actual norms follows by
smooth approximation and the separately proved zero-set support. -/
theorem difference_variance_of_regularized [IsFiniteMeasure μ] {v b K : Ω → ℝ} {p q : Ω → F}
    (hv : AEMeasurable v μ) (hb : AEMeasurable b μ) (hK : AEMeasurable K μ)
    (hp : AEStronglyMeasurable p μ) (hq : AEStronglyMeasurable q μ)
    (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2)
    (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hq0 : ∀ᵐ x ∂μ, b x = 0 → q x = 0)
    (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ) (hq2 : Integrable (fun x => ‖q x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hvariance : ∀ n, (∫ x, regularizedDifferenceValue (v x) (b x) (ε n) ^ 2 ∂μ) -
      (∫ x, regularizedDifferenceValue (v x) (b x) (ε n) ∂μ) ^ 2 ≤
        ∫ x, regularizedDifferenceEnergy (v x) (b x) (ε n) (K x) (p x) (q x) ∂μ) :
    (∫ x, (v x - b x) ^ 2 ∂μ) - (∫ x, v x - b x ∂μ) ^ 2 ≤
      ∫ x, ‖p x - q x‖ ^ 2 / K x ∂μ := by
  have h1 := integral_regularizedDifferenceValue_pow_tendsto hv hb hv2 hb2 ε hε hlim 1
  simp only [pow_one] at h1
  have h2 := integral_regularizedDifferenceValue_pow_tendsto hv hb hv2 hb2 ε hε hlim 2
  have he := integral_regularizedDifferenceEnergy_tendsto hv hb hK hp hq
    (hv2.mono (fun _ hx => hx.1)) (hb2.mono (fun _ hx => hx.1)) hK1 hp0 hq0 hp2 hq2 ε
    (fun n => (hε n).1) hlim
  exact le_of_tendsto_of_tendsto (h2.sub (h1.pow 2)) he (Filter.Eventually.of_forall hvariance)

/-- Either single norm is obtained by the same approximation, with its
own actual radial gradient and zero-set support. -/
theorem norm_variance_of_regularized [IsFiniteMeasure μ] {v K : Ω → ℝ} {p : Ω → F}
    (hv : AEMeasurable v μ) (hK : AEMeasurable K μ) (hp : AEStronglyMeasurable p μ)
    (hv2 : ∀ᵐ x ∂μ, v x ∈ Set.Icc (0 : ℝ) 2) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hp0 : ∀ᵐ x ∂μ, v x = 0 → p x = 0) (hp2 : Integrable (fun x => ‖p x‖ ^ 2) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hvariance : ∀ n, (∫ x, hRegularizedArgument (v x) (ε n) ^ 2 ∂μ) -
      (∫ x, hRegularizedArgument (v x) (ε n) ∂μ) ^ 2 ≤
        ∫ x, regularizedNormEnergy (v x) (ε n) (K x) (p x) ∂μ) :
    (∫ x, v x ^ 2 ∂μ) - (∫ x, v x ∂μ) ^ 2 ≤ ∫ x, ‖p x‖ ^ 2 / K x ∂μ := by
  have h1 := integral_regularizedNorm_pow_tendsto hv hv2 ε hε hlim 1
  simp only [pow_one] at h1
  have h2 := integral_regularizedNorm_pow_tendsto hv hv2 ε hε hlim 2
  have he := integral_regularizedNormEnergy_tendsto hv hK hp
    (hv2.mono (fun _ hx => hx.1)) hK1 hp0 hp2 ε (fun n => (hε n).1) hlim
  exact le_of_tendsto_of_tendsto (h2.sub (h1.pow 2)) he (Filter.Eventually.of_forall hvariance)

end
end PositiveEinsteinFour.Variance

end OAI
