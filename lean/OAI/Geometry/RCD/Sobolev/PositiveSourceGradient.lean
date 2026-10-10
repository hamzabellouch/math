import OAI.Geometry.RCD.Sobolev.PositiveSourceTail
import OAI.Geometry.RCD.Sobolev.PositiveSourceTest

namespace OAI

/-!
# Weighted gradient estimates for positive Poisson sources

The Cauchy--Schwarz step uses a reciprocal-weight energy and the moment
obtained from truncation. This keeps the linear dependence on source mass
which ordinary unweighted energy Cauchy--Schwarz would lose.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal Topology

noncomputable section

namespace RegularPointCoordinates

/-- Weighted Cauchy--Schwarz, including the integrability conclusion. -/
theorem integral_sq_le_reciprocal_weight {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f w : X → ℝ} (hf : AEMeasurable f μ) (hw : AEMeasurable w μ)
    (hwpos : ∀ᵐ x ∂μ, 0 < w x)
    (hiw : Integrable w μ) (hif : Integrable (fun x => f x ^ 2 / w x) μ) :
    Integrable f μ ∧ (∫ x, f x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 / w x ∂μ) * ∫ x, w x ∂μ := by
  let a := fun x => f x / Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)
  have ha : AEMeasurable a μ := hf.div hw.sqrt
  have hb : AEMeasurable b μ := hw.sqrt
  have hasq : (fun x => a x ^ 2) =ᵐ[μ] fun x => f x ^ 2 / w x := by
    filter_upwards [hwpos] with x hx
    dsimp [a]
    rw [div_pow, Real.sq_sqrt hx.le]
  have hbsq : (fun x => b x ^ 2) =ᵐ[μ] w := by
    filter_upwards [hwpos] with x hx
    exact Real.sq_sqrt hx.le
  have hma : MemLp a 2 μ :=
    (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr (hif.congr hasq.symm)
  have hmb : MemLp b 2 μ :=
    (memLp_two_iff_integrable_sq hb.aestronglyMeasurable).mpr (hiw.congr hbsq.symm)
  let A := hma.toLp a
  let B := hmb.toLp b
  have hAe : A =ᵐ[μ] a := hma.coeFn_toLp
  have hBe : B =ᵐ[μ] b := hmb.coeFn_toLp
  have he : (fun x => ⟪A x, B x⟫_ℝ) =ᵐ[μ] f := by
    filter_upwards [hAe, hBe, hwpos] with x ha hb hw
    rw [ha, hb, Real.inner_apply]
    dsimp [a, b]
    rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 hw))]
  have hAi : ‖A‖ ^ 2 = ∫ x, f x ^ 2 / w x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hAe, hasq] with x ha hs
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, ha] using hs
  have hBi : ‖B‖ ^ 2 = ∫ x, w x ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hBe, hbsq] with x hb hs
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hb] using hs
  refine ⟨(L2.integrable_inner A B).congr he, ?_⟩
  have hinner : ⟪A, B⟫_ℝ = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    exact integral_congr_ae he
  have hsq := (sq_le_sq₀ (abs_nonneg ⟪A, B⟫_ℝ) (mul_nonneg (norm_nonneg A) (norm_nonneg B))).mpr
    (abs_real_inner_le_norm A B)
  simpa only [sq_abs, hinner, mul_pow, hAi, hBi] using hsq

/-- Shifting a nonnegative function by one preserves controlled moments. -/
theorem shifted_moment_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {H : X → ℝ}
    (hH : AEMeasurable H μ) (hH0 : 0 ≤ᵐ[μ] H) {q : ℝ} (hq : 0 ≤ q)
    (hi : Integrable (fun x => H x ^ q) μ) :
    Integrable (fun x => (1 + H x) ^ q) μ ∧
      (∫ x, (1 + H x) ^ q ∂μ) ≤ 2 ^ q * (μ.real univ + ∫ x, H x ^ q ∂μ) := by
  have hb : ∀ᵐ x ∂μ, (1 + H x) ^ q ≤ 2 ^ q * (1 + H x ^ q) := by
    filter_upwards [hH0] with x hx
    change 0 ≤ H x at hx
    by_cases hle : H x ≤ 1
    · calc
        _ ≤ (2 : ℝ) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq
        _ ≤ _ := by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q,
          Real.rpow_nonneg hx q]
    · have hgt : 1 ≤ H x := (lt_of_not_ge hle).le
      calc
        _ ≤ (2 * H x) ^ q := Real.rpow_le_rpow (by linarith) (by linarith) hq
        _ = 2 ^ q * H x ^ q := Real.mul_rpow (by norm_num) hx
        _ ≤ _ := by nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q]
  have hmajor : Integrable (fun x => 2 ^ q * (1 + H x ^ q)) μ :=
    ((integrable_const (1 : ℝ)).add hi).const_mul _
  have hshift : Integrable (fun x => (1 + H x) ^ q) μ := by
    apply hmajor.mono' ((hH.const_add 1).pow_const q).aestronglyMeasurable
    filter_upwards [hH0, hb] with x hx hb
    change 0 ≤ H x at hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) q)]
    exact hb
  refine ⟨hshift, ?_⟩
  have he := integral_mono_ae hshift hmajor hb
  simpa only [integral_const_mul, integral_add (integrable_const (1 : ℝ)) hi,
    integral_const, smul_eq_mul, mul_one] using he

/-- An explicit, nonoptimal uniform constant for the normalized source. -/
def positiveSourceGradientBound (V C d q : ℝ) : ℝ :=
  1 + (2 ^ q * (V + q * (V * q⁻¹ + C ^ d * (d - q)⁻¹))) / (q - 1)

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The complete normalized positive-source L1 gradient estimate from the
Dirichlet Sobolev inequality and the source's action on bounded tests. -/
theorem normalized_positive_source_gradient (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 ≤ C)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ s) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        positiveSourceGradientBound (μ.real Ω) C d q := by
  let ν := μ.restrict Ω
  let : IsFiniteMeasure ν := ⟨by simpa only [ν, Measure.restrict_apply_univ] using hΩfin.lt_top⟩
  let U := fun x => SobolevSpace.toLp μ hQ H.val x
  let G := fun x => SobolevSpace.minimalSlope μ hQ H.val x
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hd : 0 < d := hq0.trans hqd
  have hα : 0 < q - 1 := sub_pos.mpr hq
  have hU0 : 0 ≤ᵐ[ν] U := ae_restrict_of_ae hH
  have hUm : AEMeasurable U ν := (Lp.stronglyMeasurable _).measurable.aemeasurable
  have htail (t : ℝ) (ht : 1 ≤ t) : ν {x | t ≤ U x} ≤ ENNReal.ofReal (C ^ d * t ^ (-d)) := by
    simpa only [ν, U, mul_one, one_mul] using
      dirichlet_positive_source_tail μ hQ Ω hΩfin H hH hd hC zero_le_one hsob
        (by intro φ s hs hb; simpa only [one_mul] using hsource φ s hs hb)
        (zero_lt_one.trans_le ht)
  have hUi := integrable_rpow_of_power_tail ν hUm hU0 hq0 hqd (Real.rpow_nonneg hC d) htail
  have hUb := integral_rpow_le_of_power_tail ν hUm hU0 hq0 hqd (Real.rpow_nonneg hC d) htail
  have hshift := shifted_moment_le ν hUm hU0 hq0.le hUi
  let w := fun x => (1 + U x) ^ q
  have hwpos : ∀ᵐ x ∂ν, 0 < w x := by
    filter_upwards [hU0] with x hx
    change 0 ≤ U x at hx
    exact Real.rpow_pos_of_pos (by linarith) _
  have hwm : AEMeasurable w ν := (hUm.const_add 1).pow_const q
  have hGm : AEMeasurable G ν := (Lp.stronglyMeasurable _).measurable.aemeasurable
  have hEe := positive_source_weighted_energy μ hQ Ω H hH 1
    (by intro φ s hs hb; simpa only [one_mul] using hsource φ s hs hb) hα
  have hqi : 1 + (q - 1) = q := by ring
  simp only [hqi, one_div] at hEe
  have hEg : Integrable (fun x => G x ^ 2 / w x) μ := hEe.1
  have hEn : ∀ᵐ x ∂μ, 0 ≤ G x ^ 2 / w x := by
    filter_upwards [hH] with x hx
    exact div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith) q)
  have hEl : (∫ x, G x ^ 2 / w x ∂ν) ≤ (q - 1)⁻¹ :=
    (setIntegral_le_integral hEg hEn).trans hEe.2
  have hcs := integral_sq_le_reciprocal_weight ν hGm hwm hwpos hshift.1 hEg.integrableOn
  have hV : ν.real univ = μ.real Ω := by simp only [ν, Measure.real, Measure.restrict_apply_univ]
  let M := 2 ^ q * (ν.real univ + q * (ν.real univ * q⁻¹ + C ^ d * (d - q)⁻¹))
  have hMb : (∫ x, w x ∂ν) ≤ M := by
    apply hshift.2.trans
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hUb) (Real.rpow_nonneg (by norm_num) q)
  have hsq : (∫ x, G x ∂ν) ^ 2 ≤ (q - 1)⁻¹ * M :=
    hcs.2.trans (mul_le_mul hEl hMb (integral_nonneg_of_ae (hwpos.mono fun _ hx => hx.le))
      (inv_nonneg.mpr hα.le))
  refine ⟨hcs.1, ?_⟩
  have hb : (∫ x, G x ∂ν) ≤ 1 + M / (q - 1) := by
    have hsq0 := sq_nonneg ((∫ x, G x ∂ν) - 1 / 2)
    rw [div_eq_mul_inv, mul_comm M] at ⊢
    nlinarith
  simpa only [positiveSourceGradientBound, M, hV, ν, G] using hb

/-- Scaling the normalized estimate gives linear dependence on a positive
source mass. -/
theorem positive_source_gradient_of_pos (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C P : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 ≤ C) (hP : 0 < P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        P * positiveSourceGradientBound (μ.real Ω) C d q := by
  let N : SobolevSpace.dirichlet μ hQ Ω := P⁻¹ • H
  have hN : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ N.val x := by
    change ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (P⁻¹ • H.val) x
    rw [map_smul]
    filter_upwards [hH, Lp.coeFn_smul P⁻¹ (SobolevSpace.toLp μ hQ H.val)] with x hx he
    rw [he]
    exact mul_nonneg (inv_nonneg.mpr hP.le) hx
  have hNs : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ N.val φ.val ≤ s := by
    intro φ s hs hb
    change energyForm μ hQ (P⁻¹ • H.val) φ.val ≤ s
    rw [energyForm_smul_left]
    calc
      _ ≤ P⁻¹ * (P * s) := mul_le_mul_of_nonneg_left (hsource φ s hs hb) (inv_nonneg.mpr hP.le)
      _ = s := by field_simp
  have hn := normalized_positive_source_gradient μ hQ Ω hΩfin N hN hq hqd hC hsob hNs
  have he : (fun x => P * SobolevSpace.minimalSlope μ hQ N.val x) =ᵐ[μ]
      fun x => SobolevSpace.minimalSlope μ hQ H.val x := by
    change (fun x => P * SobolevSpace.minimalSlope μ hQ (P⁻¹ • H.val) x) =ᵐ[μ] _
    rw [SobolevSpace.minimalSlope_smul_nonneg μ hQ H.val (inv_nonneg.mpr hP.le)]
    filter_upwards [Lp.coeFn_smul P⁻¹ (SobolevSpace.minimalSlope μ hQ H.val)] with x hx
    rw [hx]
    change P * (P⁻¹ * SobolevSpace.minimalSlope μ hQ H.val x) = _
    field_simp
  refine ⟨(hn.1.const_mul P).congr (ae_restrict_of_ae he), ?_⟩
  calc
    _ = ∫ x in Ω, P * SobolevSpace.minimalSlope μ hQ N.val x ∂μ :=
      integral_congr_ae (ae_restrict_of_ae he.symm)
    _ = P * ∫ x in Ω, SobolevSpace.minimalSlope μ hQ N.val x ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hn.2 hP.le

/-- The linear gradient estimate also holds at zero source mass, by
approaching that mass through positive upper bounds. -/
theorem positive_source_gradient (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C P : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        P * positiveSourceGradientBound (μ.real Ω) C d q := by
  have hb (r : ℝ) (hr : P < r) :
      IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        r * positiveSourceGradientBound (μ.real Ω) C d q := by
    apply positive_source_gradient_of_pos μ hQ Ω hΩfin H hH hq hqd hC (hP.trans_lt hr) hsob
    intro φ s hs ht
    exact (hsource φ s hs ht).trans (mul_le_mul_of_nonneg_right hr.le hs)
  refine ⟨(hb (P + 1) (by linarith)).1, ?_⟩
  have hlim : Tendsto (fun r : ℝ => r * positiveSourceGradientBound (μ.real Ω) C d q)
      (𝓝[>] P) (𝓝 (P * positiveSourceGradientBound (μ.real Ω) C d q)) :=
    (continuous_id.mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hb r hr).2

omit [ProperSpace X] in
/-- The companion square-gradient bound is the direct test by the bounded
solution itself. -/
theorem positive_source_energy (Ω : Set X) (H : SobolevSpace.dirichlet μ hQ Ω)
    {P B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x ∧ SobolevSpace.toLp μ hQ H.val x ≤ B)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s) :
    (∫ x, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 ∂μ) ≤ P * B := by
  calc
    _ = ∫ x, localGamma μ hQ H.val H.val x ∂μ :=
      integral_congr_ae (localGamma_self μ hQ H.val).symm
    _ = energyForm μ hQ H.val H.val := integral_localGamma_eq_energyForm μ hQ _ _
    _ ≤ P * B := hsource H B hB hH

/-- Both positive-source estimates, with a fixed exponent selected from
`d > 1`. The L1 bound is linear in mass; the L2 energy bound is mass times
the upper bound of the solution. -/
theorem positive_source_bounds (Ω : Set X) (hΩfin : μ Ω ≠ ∞)
    (H : SobolevSpace.dirichlet μ hQ Ω)
    {d C P B : ℝ} (hd : 1 < d) (hC : 0 ≤ C) (hP : 0 ≤ P) (hB : 0 ≤ B)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x ∧ SobolevSpace.toLp μ hQ H.val x ≤ B)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        C * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        P * positiveSourceGradientBound (μ.real Ω) C d ((1 + d) / 2) ∧
      (∫ x, (SobolevSpace.minimalSlope μ hQ H.val x) ^ 2 ∂μ) ≤ P * B := by
  have hg := positive_source_gradient μ hQ Ω hΩfin H (hH.mono fun _ hx => hx.1)
    (q := (1 + d) / 2) (by linarith) (by linarith) hC hP hsob hsource
  exact ⟨hg.1, hg.2, positive_source_energy μ hQ Ω H hB hH hsource⟩

end RegularPointCoordinates

end

end OAI
