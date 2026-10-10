import OAI.Geometry.RCD.Sobolev.HessianActionIntegral
import OAI.Geometry.RCD.Metric.IntegralSquareProduct
import OAI.Geometry.RCD.Metric.ShiftedRadonBounds

namespace OAI

/-! # From regular-core Hessian actions to all Dirichlet tests -/

open Set Filter MeasureTheory

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The action integral on the local domain is the actual continuous
Hessian functional, because all three test factors vanish off the domain. -/
theorem LocalHessianPairing.integral_action_core_on {Ω : Set X} (hΩ : MeasurableSet Ω)
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a) (φ : G.core) :
    (∫ x in Ω, localHessianAction μ hQ f a φ.val.val G.mixed
      (G.gammaF φ).val (G.gammaA φ).val x ∂μ) = G.hessian φ.val := by
  have hi : Integrable (fun x => localGamma μ hQ a (G.gammaF φ).val x+
      localGamma μ hQ φ.val.val G.mixed x) (μ.restrict Ω) :=
    ((localGamma_memL1 μ hQ a (G.gammaF φ).val).add
      (localGamma_memL1 μ hQ φ.val.val G.mixed)).integrableOn
  have hc : (∫ x in Ω, localGamma μ hQ φ.val.val G.mixed x ∂μ) =
      energyForm μ hQ φ.val.val G.mixed := by
    rw [integral_congr_ae (ae_restrict_of_ae (localGamma_comm μ hQ φ.val.val G.mixed)),
      integral_localGamma_dirichlet μ hQ Ω hΩ G.mixed φ.val,energyForm_comm]
  unfold localHessianAction
  rw [integral_div,integral_sub hi (localGamma_memL1 μ hQ f (G.gammaA φ).val).integrableOn,
    integral_add (localGamma_memL1 μ hQ a (G.gammaF φ).val).integrableOn
      (localGamma_memL1 μ hQ φ.val.val G.mixed).integrableOn,
    integral_localGamma_dirichlet μ hQ Ω hΩ a (G.gammaF φ),hc,
    integral_localGamma_dirichlet μ hQ Ω hΩ f (G.gammaA φ)]
  have hk := G.koszul φ
  linarith only [hk]

omit [ProperSpace X] in
/-- An estimate on the genuine dense regular core extends to every
Dirichlet test by continuity of the Hessian and Dirichlet forms. -/
theorem LocalHessianPairing.bound_of_core {Ω : Set X}
    {f a : SobolevSpace μ hQ} (G : LocalHessianPairing μ hQ Ω f a) (b D : ℝ)
    (hbound : ∀ φ : G.core,
      (G.hessian φ.val-b*energyForm μ hQ a φ.val.val)^2≤D*energyForm μ hQ φ.val.val φ.val.val) :
    ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ-b*energyForm μ hQ a φ.val)^2≤D*energyForm μ hQ φ.val φ.val := by
  let A : SobolevSpace.dirichlet μ hQ Ω →L[ℝ] ℝ :=
    G.hessian-b • ((sobolevEnergyForm μ hQ a).comp (SobolevSpace.dirichlet μ hQ Ω).subtypeL)
  have hJ : Continuous (fun φ : SobolevSpace.dirichlet μ hQ Ω => φ.val) :=
    (SobolevSpace.dirichlet μ hQ Ω).subtypeL.continuous
  have hP : Continuous (fun φ : SobolevSpace.dirichlet μ hQ Ω => SobolevSpace.toLp μ hQ φ.val) :=
    (SobolevSpace.toLpCLM μ hQ).continuous.comp hJ
  have hE : Continuous (fun φ : SobolevSpace.dirichlet μ hQ Ω => energyForm μ hQ φ.val φ.val) := by
    unfold energyForm
    exact (hJ.inner hJ).sub (hP.inner hP)
  have hc : IsClosed {φ : SobolevSpace.dirichlet μ hQ Ω | (A φ)^2≤D*energyForm μ hQ φ.val φ.val} :=
    isClosed_le (A.continuous.pow 2) (continuous_const.mul hE)
  have hs : (G.core : Set (SobolevSpace.dirichlet μ hQ Ω)) ⊆
      {φ | (A φ)^2≤D*energyForm μ hQ φ.val φ.val} := fun φ hφ => hbound ⟨φ,hφ⟩
  have he := closure_minimal hs hc
  rw [G.core_dense.closure_eq] at he
  exact fun φ => he (mem_univ φ)

/-- The shifted pointwise action bound gives the sharp integrated bound
with one direction cap and the full shifted Bochner mass. -/
theorem LocalHessianPairing.bound_of_core_action {Ω : Set X} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (μ.restrict Ω)] {f a : SobolevSpace μ hQ}
    (G : LocalHessianPairing μ hQ Ω f a) (σ : Measure X) [IsFiniteMeasure σ]
    (b c C : ℝ) (hC : 0≤C)
    (hden : ∀ᵐ x ∂μ.restrict Ω, c≤(σ.rnDeriv μ x).toReal)
    (hbound : ∀ φ : G.core, ∀ᵐ x ∂μ.restrict Ω,
      (localHessianAction μ hQ f a φ.val.val G.mixed (G.gammaF φ).val (G.gammaA φ).val x-
        b*localGamma μ hQ a φ.val.val x)^2 ≤
      (C*((σ.rnDeriv μ x).toReal-c))*localGamma μ hQ φ.val.val φ.val.val x) :
    ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (G.hessian φ-b*energyForm μ hQ a φ.val)^2 ≤
        (C*(σ.real Ω-c*μ.real Ω))*energyForm μ hQ φ.val φ.val := by
  apply G.bound_of_core μ hQ b (C*(σ.real Ω-c*μ.real Ω))
  intro φ
  let H := fun x => localHessianAction μ hQ f a φ.val.val G.mixed
    (G.gammaF φ).val (G.gammaA φ).val x-b*localGamma μ hQ a φ.val.val x
  have hd : Integrable (fun x => (σ.rnDeriv μ x).toReal) (μ.restrict Ω) :=
    Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ Ω)
  have hF := (hd.sub (integrable_const c)).const_mul C
  have hG := (localGamma_memL1 μ hQ φ.val.val φ.val.val).integrableOn (s := Ω)
  have hH : Integrable H (μ.restrict Ω) :=
    ((localHessianAction_integrable μ hQ _ _ _ _ _ _).sub
      ((localGamma_memL1 μ hQ a φ.val.val).const_mul b)).integrableOn
  have hF0 : ∀ᵐ x ∂μ.restrict Ω, 0≤C*((σ.rnDeriv μ x).toReal-c) :=
    hden.mono fun x hx => mul_nonneg hC (sub_nonneg.mpr hx)
  have hG0 : ∀ᵐ x ∂μ.restrict Ω, 0≤localGamma μ hQ φ.val.val φ.val.val x := by
    filter_upwards [ae_restrict_of_ae (localGamma_self μ hQ φ.val.val)] with x hx
    rw [hx]
    positivity
  have hh := integral_sq_le_of_sq_le_product (μ.restrict Ω) hF hG hH hF0 hG0 (hbound φ)
  have hHi : (∫ x in Ω, H x ∂μ) = G.hessian φ.val-b*energyForm μ hQ a φ.val.val := by
    rw [integral_sub (localHessianAction_integrable μ hQ _ _ _ _ _ _).integrableOn
      ((localGamma_memL1 μ hQ a φ.val.val).const_mul b).integrableOn,
      integral_const_mul,G.integral_action_core_on μ hQ hΩ φ,
      integral_localGamma_dirichlet μ hQ Ω hΩ a φ.val]
  have hGi := integral_localGamma_dirichlet μ hQ Ω hΩ φ.val.val φ.val
  have hFi : (∫ x in Ω, C*((σ.rnDeriv μ x).toReal-c) ∂μ) ≤ C*(σ.real Ω-c*μ.real Ω) := by
    rw [integral_const_mul,integral_sub hd (integrable_const c)]
    simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ]
    rw [mul_comm (μ.real Ω) c]
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Measure.setIntegral_toReal_rnDeriv_le (μ := σ) (ν := μ) (measure_ne_top σ Ω)) _) hC
  rw [hHi,hGi] at hh
  have he0 : 0≤energyForm μ hQ φ.val.val φ.val.val := by
    rw [energyForm_self]
    exact mul_nonneg (by norm_num) (SobolevSpace.energy_nonneg μ hQ _)
  exact hh.trans (mul_le_mul_of_nonneg_right hFi he0)

end RegularPointCoordinates

end

end OAI
