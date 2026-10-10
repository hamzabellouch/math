import OAI.Probability.BenjaminiSchramm.TiltedMagnetization

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Percolation.BenjaminiSchramm

def ghostKernel (h x : ℝ) : ℝ := 1 - Real.exp (-h * x)

lemma ghostKernel_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    0 ≤ ghostKernel h x := by
  apply sub_nonneg.mpr
  exact (Real.exp_le_one_iff).mpr (by nlinarith)

lemma ghostKernel_le_one (h x : ℝ) : ghostKernel h x ≤ 1 := by
  exact sub_le_self _ (Real.exp_pos _).le

lemma ghostKernel_le_product (h x : ℝ) : ghostKernel h x ≤ h * x := by
  have he := Real.add_one_le_exp (-h * x)
  dsimp [ghostKernel]
  linarith

lemma ghostKernel_scaled_derivative_le (h x : ℝ) :
    h * (x * Real.exp (-h * x)) ≤ ghostKernel h x := by
  have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (h * x))
    (Real.exp_pos (-h * x)).le
  have heq : Real.exp (h * x) * Real.exp (-h * x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [heq] at he
  dsimp [ghostKernel]
  nlinarith

lemma hasDerivAt_ghostKernel (h x : ℝ) :
    HasDerivAt (fun r => ghostKernel r x) (x * Real.exp (-h * x)) h := by
  have he : HasDerivAt (fun r : ℝ => Real.exp (-r * x))
      (-x * Real.exp (-h * x)) h := by
    convert (((hasDerivAt_id h).neg.mul_const x).exp) using 1
    · funext r
      rfl
    · dsimp
      ring
  convert (hasDerivAt_const h (1 : ℝ)).sub he using 1
  · rfl
  · ring

lemma ghostKernel_le_threeQuarter {h x : ℝ} (hh : 0 ≤ h) (hx : 0 ≤ x) :
    ghostKernel h x ≤ (h * x) ^ (3 / 4 : ℝ) := by
  by_cases hu : h * x ≤ 1
  · exact (ghostKernel_le_product h x).trans
      (Real.self_le_rpow_of_le_one (mul_nonneg hh hx) hu (by norm_num))
  · exact (ghostKernel_le_one h x).trans
      (Real.one_le_rpow (le_of_not_ge hu) (by norm_num))

lemma ghostKernel_quartic_moment {t x : ℝ} (ht : 0 ≤ t) (hx : 0 ≤ x) :
    ghostKernel (t ^ 4) x ≤ t ^ 3 * x ^ (3 / 4 : ℝ) := by
  have he : (t ^ 4 : ℝ) ^ (3 / 4 : ℝ) = t ^ 3 := by
    rw [← Real.rpow_natCast t 4, ← Real.rpow_mul ht]
    norm_num
  simpa only [Real.mul_rpow (pow_nonneg ht 4) hx, he] using
    ghostKernel_le_threeQuarter (pow_nonneg ht 4) hx

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℝ)

def ghostMagnetization (h : ℝ) : ℝ := ∫ ω, ghostKernel h (X ω) ∂μ

def ghostMagnetizationDerivative (h : ℝ) : ℝ :=
  ∫ ω, X ω * Real.exp (-h * X ω) ∂μ

lemma measurable_ghostKernel (hX : Measurable X) (h : ℝ) :
    Measurable (fun ω => ghostKernel h (X ω)) :=
  measurable_const.sub ((measurable_const.mul hX).exp)

lemma integrable_ghostKernel (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 ≤ h) : Integrable (fun ω => ghostKernel h (X ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_ghostKernel X hX h).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (ghostKernel_nonneg hh (hX0 ω))]
    exact ghostKernel_le_one _ _

theorem hasDerivAt_ghostMagnetization (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) :
    Integrable (fun ω => X ω * Real.exp (-h * X ω)) μ ∧
      HasDerivAt (ghostMagnetization μ X) (ghostMagnetizationDerivative μ X h) h := by
  have hhalf : 0 < h / 2 := by positivity
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi (h / 2)) (bound := fun _ => 2 / h)
    (Ioi_mem_nhds (by linarith))
    (Eventually.of_forall fun r => (measurable_ghostKernel X hX r).aestronglyMeasurable)
    (integrable_ghostKernel μ X hX hX0 hh.le)
    (hX.mul ((measurable_const.mul hX).exp)).aestronglyMeasurable
  · exact ae_of_all _ fun ω r hr => by
      have hder0 : 0 ≤ X ω * Real.exp (-r * X ω) :=
        mul_nonneg (hX0 ω) (Real.exp_pos _).le
      have hprod : r * (X ω * Real.exp (-r * X ω)) ≤ 1 :=
        (ghostKernel_scaled_derivative_le r (X ω)).trans (ghostKernel_le_one _ _)
      change h / 2 < r at hr
      rw [Real.norm_eq_abs, abs_of_nonneg hder0]
      apply (le_div_iff₀ hh).mpr
      nlinarith
  · exact integrable_const _
  · exact ae_of_all _ fun ω r _ => hasDerivAt_ghostKernel r (X ω)

omit [IsFiniteMeasure μ] in
lemma ghostMagnetization_nonneg (hX0 : ∀ ω, 0 ≤ X ω) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ ghostMagnetization μ X h :=
  integral_nonneg fun ω => ghostKernel_nonneg hh (hX0 ω)

lemma ghostMagnetization_concave_bound (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    {h : ℝ} (hh : 0 < h) :
    h * ghostMagnetizationDerivative μ X h ≤ ghostMagnetization μ X h := by
  rw [ghostMagnetizationDerivative, ← integral_const_mul]
  apply integral_mono ((hasDerivAt_ghostMagnetization μ X hX hX0 hh).1.const_mul h)
    (integrable_ghostKernel μ X hX hX0 hh.le)
  intro ω
  exact ghostKernel_scaled_derivative_le _ _

lemma ghostMagnetization_quartic_moment (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXi : Integrable (fun ω => X ω ^ (3 / 4 : ℝ)) μ) {t : ℝ} (ht : 0 ≤ t) :
    ghostMagnetization μ X (t ^ 4) ≤
      (∫ ω, X ω ^ (3 / 4 : ℝ) ∂μ) * t ^ 3 := by
  calc
    _ ≤ ∫ ω, t ^ 3 * X ω ^ (3 / 4 : ℝ) ∂μ :=
      integral_mono (integrable_ghostKernel μ X hX hX0 (pow_nonneg ht 4))
        (hXi.const_mul _) (fun ω => ghostKernel_quartic_moment ht (hX0 ω))
    _ = _ := by rw [integral_const_mul, mul_comm]

theorem firstMoment_le_of_ghost_quartic_ratio (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (B : ℝ)
    (hbound : ∀ t, 0 < t → t ≤ 1 → ghostMagnetization μ X (t ^ 4) / t ^ 4 ≤ B) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ≤ ENNReal.ofReal B := by
  let t (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  let h (n : ℕ) : ℝ := t n ^ 4
  have ht0 (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hh0 (n : ℕ) : 0 < h n := pow_pos (ht0 n) 4
  have hlim : Tendsto h atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall hh0⟩
    simpa only [h, zero_pow (by decide : 4 ≠ 0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4
  let F (n : ℕ) (ω : Ω) := ENNReal.ofReal (ghostKernel (h n) (X ω) / h n)
  have hF (n : ℕ) : Measurable (F n) :=
    ((measurable_ghostKernel X hX _).div_const _).ennreal_ofReal
  have hF_lim (ω : Ω) : Tendsto (fun n => F n ω) atTop (𝓝 (ENNReal.ofReal (X ω))) := by
    have hs := ((hasDerivAt_ghostKernel 0 (X ω)).tendsto_slope_zero_right).comp hlim
    have hs' : Tendsto (fun n => ghostKernel (h n) (X ω) / h n) atTop (𝓝 (X ω)) := by
      simpa only [Function.comp_def, zero_add, ghostKernel, neg_zero, zero_mul, mul_zero,
        Real.exp_zero, mul_one, sub_self, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs'
  calc
    _ = ∫⁻ ω, liminf (fun n => F n ω) atTop ∂μ :=
      lintegral_congr fun ω => (hF_lim ω).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ω, F n ω ∂μ) atTop := lintegral_liminf_le hF
    _ ≤ ENNReal.ofReal B := by
      apply le_trans (liminf_le_liminf (Eventually.of_forall fun n => ?_)) (liminf_const _).le
      rw [show (∫⁻ ω, F n ω ∂μ) =
          ENNReal.ofReal (ghostMagnetization μ X (h n) / h n) from ?_]
      · exact ENNReal.ofReal_le_ofReal (hbound (t n) (ht0 n) (ht1 n))
      · change (∫⁻ ω, ENNReal.ofReal (ghostKernel (h n) (X ω) / h n) ∂μ) = _
        rw [← ofReal_integral_eq_lintegral_ofReal]
        · simp only [div_eq_mul_inv, integral_mul_const]
          rfl
        · exact (integrable_ghostKernel μ X hX hX0 (hh0 n).le).div_const _
        · exact ae_of_all _ fun ω => div_nonneg
            (ghostKernel_nonneg (hh0 n).le (hX0 ω)) (hh0 n).le

theorem firstMoment_lt_top_of_threeQuarter_and_differential
    (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω)
    (hXi : Integrable (fun ω => X ω ^ (3 / 4 : ℝ)) μ)
    (C : ℝ) (hC : 0 ≤ C)
    (hdiff : ∀ t, 0 < t → t ≤ 1 →
      ghostMagnetization μ X (t ^ 4) ≤ C * ghostMagnetization μ X (t ^ 4) ^ 2 +
        t ^ 4 * ghostMagnetizationDerivative μ X (t ^ 4) +
        C * t ^ 6 * ghostMagnetizationDerivative μ X (t ^ 4)) :
    (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) < ⊤ := by
  let K := ∫ ω, X ω ^ (3 / 4 : ℝ) ∂μ
  have hK : 0 ≤ K := integral_nonneg fun ω => Real.rpow_nonneg (hX0 ω) _
  apply lt_of_le_of_lt (firstMoment_le_of_ghost_quartic_ratio μ X hX hX0
    (ghostMagnetization μ X 1 + 2 * C * K ^ 2 + 4 * C * K) ?_) ENNReal.ofReal_lt_top
  intro t ht ht1
  apply magnetization_ratio_bound_of_quartic_moment (ghostMagnetization μ X)
    (ghostMagnetizationDerivative μ X) C K hC hK
    (fun h hh => (hasDerivAt_ghostMagnetization μ X hX hX0 hh).2)
    (fun h hh => ghostMagnetization_nonneg μ X hX0 hh.le)
    (fun s hs _ => ghostMagnetization_quartic_moment μ X hX hX0 hXi hs.le)
    (fun h hh => ghostMagnetization_concave_bound μ X hX hX0 hh) hdiff t ht ht1

end Percolation.BenjaminiSchramm

end

end OAI
