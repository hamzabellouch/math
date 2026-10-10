import OAI.Analysis.Mahler.AngularIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! The bounded-convergence normalization M(r) → 1. -/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology
namespace MahlerConformal

lemma eventually_radius : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo 0 1 := Ioo_mem_nhdsLT zero_lt_one

lemma B_nonneg {r θ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hθ : θ ∈ Icc 0 Real.pi) : 0 ≤ B r θ := by
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
  have hd : 0 < 1-r^2 := by nlinarith
  unfold B
  apply mul_nonneg (by positivity)
  apply Real.arctan_nonneg.mpr
  positivity

/-- Pointwise interior-angle limit; the endpoint angles are intentionally excluded. -/
theorem B_tendsto_one {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun r => B r θ) (𝓝[<] 1) (𝓝 (2/Real.pi)) := by
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] 1) (𝓝 1) := nhdsWithin_le_nhds
  have hd0 : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hid.pow 2)
  have hd : Tendsto (fun r : ℝ => 1-r^2) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hd0, ?_⟩
    filter_upwards [eventually_radius] with r hr
    change 0 < 1-r^2
    nlinarith [hr.1, hr.2]
  have hn : Tendsto (fun r : ℝ => 2*r*Real.sin θ) (𝓝[<] 1) (𝓝 (2*Real.sin θ)) := by
    simpa using (tendsto_const_nhds.mul hid).mul_const (Real.sin θ)
  have hv : Tendsto (fun r : ℝ => 2*r*Real.sin θ/(1-r^2)) (𝓝[<] 1) atTop := by
    simpa only [div_eq_mul_inv, Pi.inv_apply] using hn.pos_mul_atTop
      (mul_pos (by norm_num) (Real.sin_pos_of_pos_of_lt_pi hθ hθπ))
      hd.inv_tendsto_nhdsGT_zero
  have ha := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hv).const_mul
    (4/Real.pi^2)
  have he : 4/Real.pi^2*(Real.pi/2) = 2/Real.pi := by field_simp; ring
  simpa only [B, he, Function.comp_apply] using ha

/-- Bounded convergence applied to the actual angular speed of F. -/
theorem integral_B_tendsto_one :
    Tendsto (fun r => ∫ θ in (0 : ℝ)..Real.pi, B r θ) (𝓝[<] 1) (𝓝 2) := by
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := 0) (b := Real.pi) (F := B) (f := fun _ => 2/Real.pi)
    (fun _ => 2/Real.pi)
    (Filter.Eventually.of_forall fun r => (continuous_B r).aestronglyMeasurable)
    (by
      filter_upwards [eventually_radius] with r hr
      exact Filter.Eventually.of_forall fun θ hθ => by
        rw [uIoc_of_le Real.pi_pos.le] at hθ
        rw [Real.norm_eq_abs, abs_of_nonneg (B_nonneg hr.1 hr.2 ⟨hθ.1.le, hθ.2⟩)]
        exact (B_lt_two_div_pi r θ).le)
    (intervalIntegrable_const)
    (by
      filter_upwards [(Ioo_ae_eq_Ioc (μ := volume) (a := (0 : ℝ)) (b := Real.pi))] with θ heq
      intro hθ
      rw [uIoc_of_le Real.pi_pos.le] at hθ
      have hi : θ ∈ Ioo (0 : ℝ) Real.pi := heq.mpr hθ
      exact B_tendsto_one hi.1 hi.2)
  have he : (∫ _θ in (0 : ℝ)..Real.pi, 2/Real.pi) = 2 := by
    simp [intervalIntegral.integral_const, smul_eq_mul, Real.pi_ne_zero]
  rwa [he] at ht

/-- The real part of M(r)=F(r) tends to 1.
No radial derivative or assumed endpoint normalization is used. -/
theorem F_real_tendsto_one :
    Tendsto (fun r : ℝ => (F (r : ℂ)).re) (𝓝[<] 1) (𝓝 1) := by
  have ht := integral_B_tendsto_one.div_const 2
  have he : ∀ᶠ r : ℝ in 𝓝[<] 1,
      (∫ θ in (0 : ℝ)..Real.pi, B r θ)/2 = (F (r : ℂ)).re := by
    filter_upwards [eventually_radius] with r hr
    rw [integral_B_semicircle hr.1 hr.2]
    ring
  simpa using ht.congr' he

end MahlerConformal

end

end OAI
