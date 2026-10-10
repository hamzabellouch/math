import OAI.Geometry.RCD.Transport.LocalizedPlanEnergy
import OAI.Analysis.RCDHeat.SobolevTestPlan

namespace OAI

/-! # Local energy bounds with the actual transport cost

The mean endpoint variation is controlled by the quadratic transport cost,
rather than the largest displacement of the plan. The energy is restricted
to the region containing its time marginals.
-/

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace ENNReal
noncomputable section
namespace RegularPointCoordinates

private theorem integral_mul_square_le {A : Type*} [MeasurableSpace A] (μ : Measure A)
    {f g : A → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2≤(∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  let F := hf.toLp f
  let G := hg.toLp g
  have hfg : ⟪F,G⟫_ℝ=∫ x, f x*g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
    simp only [F,G,Real.inner_apply,hx,hy]
  have hff : ⟪F,F⟫_ℝ=∫ x, f x^2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [F,Real.inner_apply,hx,pow_two]
  have hgg : ⟪G,G⟫_ℝ=∫ x, g x^2 ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    simp only [G,Real.inner_apply,hx,pow_two]
  have hh := real_inner_mul_inner_self_le F G
  rw [hfg,hff,hgg] at hh
  simpa only [pow_two] using hh

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem testPlan_local_flux_square_le (μ : Measure X) (π : Measure C(Time,X))
    {C : ℝ≥0∞} (hC : C≠⊤)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x∈Ω)
    (G : Lp ℝ 2 μ) (t : Time) :
    (∫ γ : C(Time,X), dist (γ 0) (γ 1)*G (γ t) ∂π)^2≤
      (∫ γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π)*(C.toReal*∫ x in Ω, G x^2 ∂μ) := by
  have hGt := compressionPullback_memLp μ π _ (measurable_path_eval t) hC (hcomp t) G
  have hbound : (∫ γ : C(Time,X), G (γ t)^2 ∂π)≤C.toReal*∫ x in Ω, G x^2 ∂μ := by
    have hm : AEStronglyMeasurable (fun x : X => G x^2) (π.map (fun γ => γ t)) :=
      ((Lp.stronglyMeasurable G).pow 2).aestronglyMeasurable
    rw [← integral_map (measurable_path_eval t).aemeasurable hm]
    have hh := integral_mono_measure ((compression_iff_localized μ _ (hstay t) C).mp (hcomp t))
      (ae_of_all _ fun x => sq_nonneg (G x)) ((Lp.memLp G).integrable_sq.integrableOn.smul_measure hC)
    simpa only [integral_smul_measure,smul_eq_mul] using hh
  exact (integral_mul_square_le π hD hGt).trans
    (mul_le_mul_of_nonneg_left hbound (integral_nonneg fun _ => sq_nonneg _))

theorem IsRelaxedSlope.testPlan_cost_energy (μ : Measure X) [ProperSpace X] [μ.Regular]
    (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ) {C : ℝ≥0∞} (hC : C≠⊤)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤C • μ)
    (hD : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 π)
    {Ω : Set X} (hstay : ∀ t : Time, ∀ᵐ x ∂π.map (fun γ => γ t), x∈Ω)
    {u G : Lp ℝ 2 μ} (hG : IsRelaxedSlope μ u G) :
    (∫ γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π)^2≤
      (∫ γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π)*(C.toReal*∫ x in Ω, G x^2 ∂μ) := by
  let A := (∫ γ : C(Time,X), dist (γ 0) (γ 1)^2 ∂π)*(C.toReal*∫ x in Ω, G x^2 ∂μ)
  have hA : 0≤A := mul_nonneg (integral_nonneg fun _ => sq_nonneg _)
    (mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun _ => sq_nonneg _))
  let F := fun t : ℝ => ∫ γ : C(Time,X), dist (γ 0) (γ 1)*G (geodesicExtension γ t) ∂π
  have hF : Continuous F := testPlan_flux_continuous μ π hgeo hC hcomp hD G
  have hFb (t : ℝ) : F t≤Real.sqrt A := by
    have hh := testPlan_local_flux_square_le μ π hC hcomp hD hstay G
      (Set.projIcc 0 1 zero_le_one t)
    change F t^2≤A at hh
    nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A]
  have hi : (∫ t in (0:ℝ)..1, F t)≤Real.sqrt A := by
    rw [intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
    calc (∫ t in Icc (0:ℝ) 1, F t)≤∫ _ in Icc (0:ℝ) 1, Real.sqrt A :=
        integral_mono hF.integrableOn_Icc (integrable_const _) hFb
      _ = Real.sqrt A := by simp
  have he := (hG.testPlan_integrated_subinterval μ π hgeo hC hcomp hD 1).trans hi
  have hn : 0≤∫ γ : C(Time,X), |u (γ 1)-u (γ 0)| ∂π :=
    integral_nonneg fun _ => abs_nonneg _
  exact (pow_le_pow_left₀ hn he 2).trans_eq (Real.sq_sqrt hA)

end RegularPointCoordinates

end

end OAI
