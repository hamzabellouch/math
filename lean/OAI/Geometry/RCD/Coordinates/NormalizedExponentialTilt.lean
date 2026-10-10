import OAI.Geometry.RCD.Heat.CompactExponentialMultiplier

namespace OAI

/-! # Normalized positive Sobolev perturbations with controlled mass -/

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

 theorem SobolevSpace.exists_normalized_exp_tilt (ρ : SobolevSpace μ hQ)
    (hρ : ∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ ρ x)
    (hi : Integrable (SobolevSpace.toLp μ hQ ρ) μ)
    (hm : (∫ x, SobolevSpace.toLp μ hQ ρ x ∂μ)=1)
    {g : X → ℝ} {C M : ℝ≥0} (hg : LipschitzWith C g) (hgs : HasCompactSupport g)
    (hgb : ∀ x, |g x| ≤ M) (t : ℝ) :
    ∃ Z : ℝ, 0 < Z ∧ Real.exp (-|t| *M) ≤ Z ∧ Z ≤ Real.exp (|t| *M) ∧
      ∃ σ : SobolevSpace μ hQ,
        (SobolevSpace.toLp μ hQ σ =ᵐ[μ] fun x =>
          Z⁻¹*(Real.exp (t*g x)*SobolevSpace.toLp μ hQ ρ x)) ∧
        (∀ᵐ x ∂μ, 0 < SobolevSpace.toLp μ hQ σ x) ∧
        Integrable (SobolevSpace.toLp μ hQ σ) μ ∧
        (∫ x, SobolevSpace.toLp μ hQ σ x ∂μ)=1 := by
  obtain ⟨u,hu⟩ := ρ.exists_exp_mul μ hQ hg hgs hgb t
  have hbounds (x : X) : Real.exp (-|t| *M) ≤ Real.exp (t*g x) ∧
      Real.exp (t*g x) ≤ Real.exp (|t| *M) := by
    have hb : |t*g x| ≤ |t| *M := by rw [abs_mul]; gcongr; exact hgb x
    exact ⟨Real.exp_le_exp.mpr (by linarith [(abs_le.mp hb).1]),
      Real.exp_le_exp.mpr (abs_le.mp hb).2⟩
  have hui : Integrable (SobolevSpace.toLp μ hQ u) μ := by
    apply (hi.const_mul (Real.exp (|t| *M))).mono' (Lp.aestronglyMeasurable _)
    filter_upwards [hu,hρ] with x hx hp
    rw [hx,Real.norm_eq_abs,abs_of_pos (mul_pos (Real.exp_pos _) hp)]
    exact mul_le_mul_of_nonneg_right (hbounds x).2 hp.le
  have hlo : Real.exp (-|t| *M) ≤ ∫ x, SobolevSpace.toLp μ hQ u x ∂μ := by
    calc
      _ = ∫ x, Real.exp (-|t| *M)*SobolevSpace.toLp μ hQ ρ x ∂μ := by rw [integral_const_mul,hm,mul_one]
      _ ≤ _ := by
        apply integral_mono_ae (hi.const_mul _) hui
        filter_upwards [hu,hρ] with x hx hp
        rw [hx]
        exact mul_le_mul_of_nonneg_right (hbounds x).1 hp.le
  have hhi : (∫ x, SobolevSpace.toLp μ hQ u x ∂μ) ≤ Real.exp (|t| *M) := by
    calc
      _ ≤ ∫ x, Real.exp (|t| *M)*SobolevSpace.toLp μ hQ ρ x ∂μ := by
        apply integral_mono_ae hui (hi.const_mul _)
        filter_upwards [hu,hρ] with x hx hp
        rw [hx]
        exact mul_le_mul_of_nonneg_right (hbounds x).2 hp.le
      _ = _ := by rw [integral_const_mul,hm,mul_one]
  let Z := ∫ x, SobolevSpace.toLp μ hQ u x ∂μ
  have hZ : 0 < Z := (Real.exp_pos _).trans_le hlo
  let σ := Z⁻¹ • u
  have hs : SobolevSpace.toLp μ hQ σ =ᵐ[μ] fun x => Z⁻¹*SobolevSpace.toLp μ hQ u x := by
    exact Lp.coeFn_smul Z⁻¹ (SobolevSpace.toLp μ hQ u)
  have hsi : Integrable (SobolevSpace.toLp μ hQ σ) μ := (hui.const_mul Z⁻¹).congr hs.symm
  refine ⟨Z,hZ,hlo,hhi,σ,hs.trans ?_,?_,hsi,?_⟩
  · exact hu.fun_comp (fun a => Z⁻¹*a)
  · filter_upwards [hs,hu,hρ] with x hs hu hp
    rw [hs,hu]
    exact mul_pos (inv_pos.mpr hZ) (mul_pos (Real.exp_pos _) hp)
  · rw [integral_congr_ae hs,integral_const_mul]
    exact inv_mul_cancel₀ hZ.ne'

end RegularPointCoordinates

end

end OAI
