import OAI.Geometry.RCD.Sobolev.BalancedSourceGradient

namespace OAI

/-! # Linear positive-source bounds in normalized ball units -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A normalized Sobolev inequality gives a linear source-mass estimate
with a constant proportional to the square root of the length-squared scale. -/
theorem normalized_source_gradient_of_pos (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (hvol : 0 < μ.real Ω) (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C s P : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 < C) (hs : 0 < s) (hP : 0 < P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        (C * s * (μ.real Ω) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ t : ℝ, 0 ≤ t →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ t) →
      energyForm μ hQ H.val φ.val ≤ P * t) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        P * Real.sqrt (balancedGradientConstant d q * C * s) := by
  let V := μ.real Ω
  let Cs := C * s * V ^ (1 / d - 1)
  let PN := V / (C * s)
  have hPN : 0 < PN := div_pos hvol (mul_pos hC hs)
  let alpha := PN / P
  have halpha : 0 < alpha := div_pos hPN hP
  let N : SobolevSpace.dirichlet μ hQ Ω := alpha • H
  have hN : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ N.val x := by
    change ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (alpha • H.val) x
    rw [map_smul]
    filter_upwards [hH, Lp.coeFn_smul alpha (SobolevSpace.toLp μ hQ H.val)] with x hx he
    rw [he]
    exact mul_nonneg halpha.le hx
  have hNs : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ t : ℝ, 0 ≤ t →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ t) →
      energyForm μ hQ N.val φ.val ≤ PN * t := by
    intro φ t ht hb
    change energyForm μ hQ (alpha • H.val) φ.val ≤ _
    rw [energyForm_smul_left]
    calc
      _ ≤ alpha * (P * t) := mul_le_mul_of_nonneg_left (hsource φ t ht hb) halpha.le
      _ = _ := by dsimp only [alpha]; field_simp
  have hCs : 0 ≤ Cs := by dsimp only [Cs]; positivity
  have hbalance : (Cs * PN) ^ d ≤ V := by
    have he : Cs * PN = V ^ (1 / d) := by
      calc
        _ = V ^ (1 / d - 1) * V := by dsimp only [Cs, PN]; field_simp
        _ = V ^ (1 / d) := by
          calc
            _ = V ^ (1 / d - 1) * V ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = V ^ ((1 / d - 1) + 1) := (Real.rpow_add hvol _ _).symm
            _ = _ := by congr 1; ring
    rw [he, one_div, Real.rpow_inv_rpow hvol.le (ne_of_gt (zero_lt_one.trans (hq.trans hqd)))]
  have hn := balanced_positive_source_gradient μ hQ Ω hfin N hN hq hqd hCs hPN.le hsob hNs hbalance
  have he : (fun x => SobolevSpace.minimalSlope μ hQ N.val x) =ᵐ[μ]
      fun x => alpha * SobolevSpace.minimalSlope μ hQ H.val x := by
    change (fun x => SobolevSpace.minimalSlope μ hQ (alpha • H.val) x) =ᵐ[μ] _
    rw [SobolevSpace.minimalSlope_smul_nonneg μ hQ H.val halpha.le]
    exact Lp.coeFn_smul alpha (SobolevSpace.minimalSlope μ hQ H.val)
  have he' : (fun x => alpha⁻¹ * SobolevSpace.minimalSlope μ hQ N.val x) =ᵐ[μ]
      fun x => SobolevSpace.minimalSlope μ hQ H.val x := by
    filter_upwards [he] with x hx
    rw [hx]
    field_simp
  have hi : IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ :=
    (hn.1.const_mul alpha⁻¹).congr (ae_restrict_of_ae he')
  have hI : (∫ x in Ω, SobolevSpace.minimalSlope μ hQ N.val x ∂μ) =
      alpha * ∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ := by
    rw [integral_congr_ae (ae_restrict_of_ae he), integral_const_mul]
  have hb := mul_le_mul_of_nonneg_left hn.2 (sq_nonneg (P / PN))
  have hleft : (P / PN) ^ 2 * (∫ x in Ω, SobolevSpace.minimalSlope μ hQ N.val x ∂μ) ^ 2 =
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ^ 2 := by
    rw [hI]
    dsimp only [alpha]
    field_simp
  have hright : (P / PN) ^ 2 * (PN * V * balancedGradientConstant d q) =
      P ^ 2 * (balancedGradientConstant d q * C * s) := by
    dsimp only [PN]
    field_simp [ne_of_gt (show 0 < V from hvol)]
  change (P / PN) ^ 2 * (∫ x in Ω, SobolevSpace.minimalSlope μ hQ N.val x ∂μ) ^ 2 ≤
    (P / PN) ^ 2 * (PN * V * balancedGradientConstant d q) at hb
  rw [hleft, hright] at hb
  have hD : 0 ≤ balancedGradientConstant d q * C * s := by
    exact mul_nonneg (mul_nonneg (balancedGradientConstant_pos hq hqd).le hC.le) hs.le
  have hsq := Real.sq_sqrt hD
  refine ⟨hi, ?_⟩
  have hpbound : 0 ≤ P * Real.sqrt (balancedGradientConstant d q * C * s) := by positivity
  apply le_of_sq_le_sq _ hpbound
  simpa only [mul_pow, hsq] using hb

/-- The scale-correct linear bound also includes zero source mass. -/
theorem normalized_source_gradient (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (hvol : 0 < μ.real Ω) (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x)
    {d q C s P : ℝ} (hq : 1 < q) (hqd : q < d) (hC : 0 < C) (hs : 0 < s) (hP : 0 ≤ P)
    (hsob : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
        (C * s * (μ.real Ω) ^ (1 / d - 1)) * energyForm μ hQ φ.val φ.val)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ t : ℝ, 0 ≤ t →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ t) →
      energyForm μ hQ H.val φ.val ≤ P * t) :
    IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        P * Real.sqrt (balancedGradientConstant d q * C * s) := by
  have hb (r : ℝ) (hr : P < r) :
      IntegrableOn (fun x => SobolevSpace.minimalSlope μ hQ H.val x) Ω μ ∧
      (∫ x in Ω, SobolevSpace.minimalSlope μ hQ H.val x ∂μ) ≤
        r * Real.sqrt (balancedGradientConstant d q * C * s) := by
    apply normalized_source_gradient_of_pos μ hQ Ω hfin hvol H hH hq hqd hC hs
      (hP.trans_lt hr) hsob
    intro φ t ht hbound
    exact (hsource φ t ht hbound).trans (mul_le_mul_of_nonneg_right hr.le ht)
  refine ⟨(hb (P + 1) (by linarith)).1, ?_⟩
  have hlim : Tendsto (fun r : ℝ => r * Real.sqrt (balancedGradientConstant d q * C * s))
      (𝓝[>] P) (𝓝 (P * Real.sqrt (balancedGradientConstant d q * C * s))) :=
    (continuous_id.mul continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hb r hr).2

end RegularPointCoordinates

end

end OAI
