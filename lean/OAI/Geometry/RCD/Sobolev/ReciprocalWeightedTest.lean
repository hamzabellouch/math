import OAI.Geometry.RCD.Heat.ShiftedLogarithmPairing

namespace OAI

/-! # A bounded reciprocal-weighted Sobolev test

The reciprocal itself need not be in L². Its centered composition and
the original test construct their product, with the exact Gamma rule.
-/

open Set Filter MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem reciprocal_weighted_test (u w : SobolevSpace μ hQ)
    {ε : ℝ} (hε : 0<ε) (A C : ℝ≥0)
    (hu : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ u x∈Icc 0 (A:ℝ))
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ w x|≤C) :
    ∃ (J : SobolevSpace μ hQ) (B : ℝ≥0),
      (SobolevSpace.toLp μ hQ J =ᵐ[μ] fun x =>
        SobolevSpace.toLp μ hQ w x/(ε+SobolevSpace.toLp μ hQ u x)) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ J x|≤B) ∧
      (localGamma μ hQ u J =ᵐ[μ] fun x =>
        localGamma μ hQ u w x/(ε+SobolevSpace.toLp μ hQ u x)-
        SobolevSpace.toLp μ hQ w x*localGamma μ hQ u u x /
          (ε+SobolevSpace.toLp μ hQ u x)^2) := by
  obtain ⟨v,B,hv,hB,hΓv⟩ := shifted_reciprocal_sobolev μ hQ u hε A hu
  let P := SobolevSpace.product μ hQ w v C B
  let J := P+ε⁻¹ • w
  have hJ : SobolevSpace.toLp μ hQ J =ᵐ[μ] fun x =>
      SobolevSpace.toLp μ hQ w x/(ε+SobolevSpace.toLp μ hQ u x) := by
    filter_upwards [SobolevSpace.product_coe μ hQ w v C B hw hB,hv,
      Lp.coeFn_add (SobolevSpace.toLp μ hQ P) (ε⁻¹ • SobolevSpace.toLp μ hQ w),
      Lp.coeFn_smul ε⁻¹ (SobolevSpace.toLp μ hQ w)] with x hp hvx ha hs
    change SobolevSpace.toLp μ hQ P x = _ at hp
    change (SobolevSpace.toLp μ hQ P+ε⁻¹ • SobolevSpace.toLp μ hQ w) x = _
    simp only [ha,Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,hp,hvx]
    ring
  refine ⟨J,⟨ε⁻¹,inv_nonneg.mpr hε.le⟩*C,hJ,?_,?_⟩
  · filter_upwards [hJ,hu,hw] with x hx hy hz
    rw [hx,abs_div,abs_of_pos (add_pos_of_pos_of_nonneg hε hy.1)]
    change _ ≤ ε⁻¹*(C:ℝ)
    calc
      _ ≤ (C:ℝ)/(ε+SobolevSpace.toLp μ hQ u x) :=
        div_le_div_of_nonneg_right hz (add_nonneg hε.le hy.1)
      _ ≤ (C:ℝ)/ε := div_le_div_of_nonneg_left C.coe_nonneg hε (le_add_of_nonneg_right hy.1)
      _ = _ := by ring
  · have hγv : localGamma μ hQ u v =ᵐ[μ] fun x =>
        -localGamma μ hQ u u x/(ε+SobolevSpace.toLp μ hQ u x)^2 :=
      (localGamma_comm μ hQ u v).trans (hΓv u)
    filter_upwards [localGamma_add_right μ hQ u P (ε⁻¹ • w),
      localGamma_smul_right μ hQ ε⁻¹ u w,
      localGamma_product_right μ hQ u w v C B hw hB,hv,hγv] with x ha hs hp hvx hγ
    rw [ha,hs,hp,hvx,hγ]
    ring

end RegularPointCoordinates

end

end OAI
