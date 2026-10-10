import OAI.Geometry.RCD.Transport.PrescribedPlanCompression
import OAI.Geometry.RCD.Metric.LowerCurvatureVolume

namespace OAI

/-! # Scale-uniform short-distance compression from the curvature bound -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates

theorem curvature_scaled_sqrt_le_one {K r : ℝ} {n : ℕ}
    (hn : 2≤n) (hK : K≤0) (hr : 0≤r) (hcurv : -1≤K*r^2) :
    r*Real.sqrt (|K|/((n:ℝ)-1))≤1 := by
  have hn' : (2:ℝ)≤n := by exact_mod_cast hn
  have hd : 0<(n:ℝ)-1 := by linarith
  have ha : 0≤r*Real.sqrt (|K|/((n:ℝ)-1)) := mul_nonneg hr (Real.sqrt_nonneg _)
  have he : (r*Real.sqrt (|K|/((n:ℝ)-1)))^2*((n:ℝ)-1)= -K*r^2 := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg (abs_nonneg K) hd.le),abs_of_nonpos hK]
    field_simp
  have hsq : (r*Real.sqrt (|K|/((n:ℝ)-1)))^2≤1 := by
    have hh := mul_le_mul_of_nonneg_left (show (1:ℝ)≤(n:ℝ)-1 by linarith)
      (sq_nonneg (r*Real.sqrt (|K|/((n:ℝ)-1))))
    rw [mul_one,he] at hh
    linarith
  nlinarith

theorem compressionBudget_le_uniform {K r d : ℝ} {n : ℕ}
    (hn : 2≤n) (hK : K≤0) (hr : 0≤r) (hd : 0≤d) (hcurv : -1≤K*r^2)
    (C : ℝ≥0∞) :
    compressionBudget K n (d*r) C≤ENNReal.ofReal (Real.exp ((n:ℝ)*2*d))*C := by
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have hb := curvature_scaled_sqrt_le_one hn hK hr hcurv
  have he : (n:ℝ)*(2*(d*r))*Real.sqrt (|K|/((n:ℝ)-1))≤(n:ℝ)*2*d := by
    have hh := mul_le_mul_of_nonneg_left hb
      (mul_nonneg (mul_nonneg hn0 (by norm_num : (0:ℝ)≤2)) hd)
    nlinarith only [hh]
  unfold compressionBudget compressionStep
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr he)) le_rfl

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.prescribed_plan_uniform_compression {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C B : ℝ≥0∞} (hC : C≠⊤) (hB : B≠⊤)
    (h0 : ν₀≤C • hausdorff n X) (h1 : ν₁≤C • hausdorff n X)
    (p : X) {R d r : ℝ} (hR : 0≤R) (hd : 0≤d) (hr : 0≤r) (hcurv : -1≤K*r^2)
    (hs0 : ∀ᵐ x ∂ν₀, dist x p≤R) (hs1 : ∀ᵐ x ∂ν₁, dist x p≤R)
    (hD : OptimalPlanDistanceBound ν₀ ν₁ (d*r))
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0,γ 1))))
    (hc : ∀ t : Time, π.map (fun γ => γ t)≤B • hausdorff n X) :
    ∀ t : Time, π.map (fun γ => γ t)≤
      (ENNReal.ofReal (Real.exp ((n:ℝ)*2*d))*C) • hausdorff n X := by
  have hcap : compressionBudget (if K≤0 then K else 0) n (d*r) C≤
      ENNReal.ofReal (Real.exp ((n:ℝ)*2*d))*C := by
    by_cases hK : K≤0
    · simpa only [ite_eq_left hK] using compressionBudget_le_uniform hn hK hr hd hcurv C
    · simp only [ite_eq_right hK,compressionBudget,compressionStep,abs_zero,zero_div,
        Real.sqrt_zero,mul_zero,Real.exp_zero,ENNReal.ofReal_one,one_mul]
      apply le_mul_of_one_le_left'
      exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp_iff.mpr (by positivity))
  have happly : ∀ t : Time, π.map (fun γ => γ t)≤
      compressionBudget (if K≤0 then K else 0) n (d*r) C • hausdorff n X := by
    by_cases hK : K≤0
    · simpa only [ite_eq_left hK] using hX.prescribed_plan_compression hn ν₀ ν₁ hC hB h0 h1 p hR
        (mul_nonneg hd hr) hs0 hs1 hD π hg hp hc
    · let hZ := hX.zero_of_nonneg_curvature hn (le_of_not_ge hK)
      simpa only [ite_eq_right hK] using hZ.prescribed_plan_compression hn ν₀ ν₁ hC hB h0 h1 p hR
        (mul_nonneg hd hr) hs0 hs1 hD π hg hp hc
  intro t
  apply (happly t).trans
  intro A
  exact mul_le_mul' hcap le_rfl

end RegularPointCoordinates

end

end OAI
