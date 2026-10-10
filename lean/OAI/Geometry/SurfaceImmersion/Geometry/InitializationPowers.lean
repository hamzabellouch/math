import OAI.Geometry.SurfaceImmersion.Geometry.FixedOrderThreshold

namespace OAI

/-! The strict powers needed by the initialization in exact-correction.tex. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

/-- With the paper's initial amplitude `δ = z^(10*μ)`, contraction of a
map of C² size `O(z⁻²)` is smaller than the radius `z⁴`. An input metric
error of order `N > 20*μ` becomes small after normalization by `δ²`. -/
theorem initialization_power_threshold {μ N C a : ℝ} (hμ : 1 < μ)
    (hN : 20*μ < N) (ha : 0 < a) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
      C*z^(20*μ-2) ≤ z^4/8 ∧ C*z^(N-20*μ) < a := by
  obtain ⟨η₁,hη₁,hη₁1,h₁⟩ := positive_power_threshold C (20*μ-6) (1/8)
    (by linarith) (by norm_num)
  obtain ⟨η₂,hη₂,_,h₂⟩ := positive_power_threshold C (N-20*μ) a
    (by linarith) ha
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,(min_le_left _ _).trans hη₁1,?_⟩
  intro z hz hzη
  refine ⟨?_,h₂ z hz (hzη.trans_le (min_le_right _ _))⟩
  have hh := mul_le_mul_of_nonneg_right (h₁ z hz (hzη.trans_le (min_le_left _ _))).le
    (pow_nonneg hz.le 4)
  have he : C*z^(20*μ-2) = (C*z^(20*μ-6))*z^4 := by
    rw [show 20*μ-2 = (20*μ-6)+4 by ring,Real.rpow_add hz,Real.rpow_ofNat]
    ring
  rw [he]
  linarith

/-- The finite first-block input budget in the paper's original weighted
scale. No loss proportional to the differentiation order is introduced. -/
theorem initialization_budget_threshold {μ N C D e : ℝ} (hμ : 1 < μ)
    (hN : 20*μ < N) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 < e) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/32 ∧ ∀ z : ℝ, 0 < z → z < η →
      z^μ ≤ z ∧ z^μ ≤ 1/32 ∧
      C/z^2+(z^μ/z)*(C/z^2) ≤ 1/z^4 ∧
      D+z^μ*D+e ≤ 1/z^4 ∧
      z^(20*μ)*(C/z^2) ≤ z^4/8 ∧
      C*z^N ≤ z^(20*μ)*e := by
  obtain ⟨η₀,hη₀,_,hp⟩ := initialization_power_threshold (C := C) hμ hN he
  obtain ⟨η₁,hη₁,_,h₁⟩ := positive_power_threshold (2*C) 2 1 (by norm_num) zero_lt_one
  obtain ⟨η₂,hη₂,_,h₂⟩ := positive_power_threshold (2*D+e) 4 1 (by norm_num) zero_lt_one
  let η := min (1/32) (min η₀ (min η₁ η₂))
  refine ⟨η,lt_min (by norm_num) (lt_min hη₀ (lt_min hη₁ hη₂)),min_le_left _ _,?_⟩
  intro z hz hzη
  have hz32 : z ≤ 1/32 := hzη.le.trans (min_le_left _ _)
  have hz1 : z ≤ 1 := by linarith
  have hη := hzη.trans_le (min_le_right _ _)
  have hz₀ : z < η₀ := hη.trans_le (min_le_left _ _)
  have hη' := hη.trans_le (min_le_right _ _)
  have hz₁ : z < η₁ := hη'.trans_le (min_le_left _ _)
  have hz₂ : z < η₂ := hη'.trans_le (min_le_right _ _)
  have ht : z^μ ≤ z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hμ.le
  have hratio : z^μ/z ≤ 1 := (div_le_one hz).mpr ht
  have hsmall₁ : (2*C)*z^2 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (h₁ z hz hz₁).le
  have hsmall₂ : (2*D+e)*z^4 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (h₂ z hz hz₂).le
  have hbudget : 2*C/z^2 ≤ 1/z^4 := by
    apply (div_le_div_iff₀ (pow_pos hz 2) (pow_pos hz 4)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall₁) (sq_nonneg z)]
  have hmetric : 2*D+e ≤ 1/z^4 := (le_div_iff₀ (pow_pos hz 4)).mpr hsmall₂
  obtain ⟨hdisp,herr⟩ := hp z hz hz₀
  have hpower : z^(20*μ)*(C/z^2) = C*z^(20*μ-2) := by
    rw [Real.rpow_sub hz,Real.rpow_ofNat]
    ring
  have herror : C*z^N = (C*z^(N-20*μ))*z^(20*μ) := by
    rw [mul_assoc,← Real.rpow_add hz]
    congr 2
    ring
  refine ⟨ht,ht.trans hz32,?_,?_,?_,?_⟩
  · calc
      C/z^2+(z^μ/z)*(C/z^2) ≤ C/z^2+1*(C/z^2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio (div_nonneg hC (sq_nonneg z)))
      _ = 2*C/z^2 := by ring
      _ ≤ 1/z^4 := hbudget
  · exact (by nlinarith [mul_le_mul_of_nonneg_right (ht.trans hz1) hD] :
      D+z^μ*D+e ≤ 2*D+e).trans hmetric
  · rwa [hpower]
  · rw [herror]
    exact (mul_le_mul_of_nonneg_right herr.le (Real.rpow_nonneg hz.le _)).trans_eq (mul_comm _ _)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
