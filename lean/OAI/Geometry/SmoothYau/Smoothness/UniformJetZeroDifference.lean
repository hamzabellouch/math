import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.SmoothFiniteWaveSum

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace YauCounterexamples
section PhaseNearWeight
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma uniform_jet_zero_difference (S F : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hS0 : ∀ p, S p 0 = F p 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hFB : UniformJetBounds F univ (Metric.closedBall 0 1)) :
    ∃ C > 0, ∀ p x, x ∈ Metric.closedBall 0 1 → ‖S p x-F p x‖ ≤ C*‖x‖ := by
  obtain ⟨C1,hC1,hb1⟩ := hSB 1
  obtain ⟨C2,hC2,hb2⟩ := hFB 1
  refine ⟨C1+C2,add_pos hC1 hC2,?_⟩
  intro p x hx
  have hs : ‖S p x-S p 0‖ ≤ C1*‖x‖ := by
    have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hS p).differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hb1 p (mem_univ _) y hy)
      (Metric.mem_closedBall_self zero_le_one) hx
    simpa only [sub_zero] using hh
  have hf : ‖F p x-F p 0‖ ≤ C2*‖x‖ := by
    have hh := (convex_closedBall (0 : E) 1).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hF p).differentiable (by simp) y)
      (fun y hy => by simpa only [norm_iteratedFDeriv_one] using hb2 p (mem_univ _) y hy)
      (Metric.mem_closedBall_self zero_le_one) hx
    simpa only [sub_zero] using hh
  have he : S p x-F p x = (S p x-S p 0)-(F p x-F p 0) := by rw [hS0]; ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hs hf).trans_eq (by ring))

theorem phase_exp_near_weight (S F : X → E → ℂ)
    (hS : ∀ p, ContDiff ℝ ∞ (S p)) (hF : ∀ p, ContDiff ℝ ∞ (F p))
    (hS0 : ∀ p, S p 0 = F p 0)
    (hSB : UniformJetBounds S univ (Metric.closedBall 0 1))
    (hFB : UniformJetBounds F univ (Metric.closedBall 0 1)) :
    ∃ c > 0, ∀ p (n : ℝ), 1 ≤ n → ∀ x : E, ‖x‖ ≤ 1/n →
      c*Real.exp (n*(F p x).re) ≤ ‖Complex.exp ((n : ℂ)*S p x)‖ := by
  obtain ⟨C,hC,hb⟩ := uniform_jet_zero_difference S F hS hF hS0 hSB hFB
  refine ⟨Real.exp (-C),Real.exp_pos _,?_⟩
  intro p n hn x hx
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hxball : x ∈ Metric.closedBall (0 : E) 1 := by
    simp only [Metric.mem_closedBall,dist_zero_right]
    exact hx.trans (by simpa only [one_div] using (inv_le_one₀ hn0).mpr hn)
  have hh : ‖S p x-F p x‖ ≤ C/n :=
    (hb p x hxball).trans (by simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_left hx hC.le)
  have hre : (F p x).re-(S p x).re ≤ C/n := by
    have ht := Complex.re_le_norm (F p x-S p x)
    rw [Complex.sub_re,norm_sub_rev] at ht
    exact ht.trans hh
  have he : -C+n*(F p x).re ≤ n*(S p x).re := by
    have he' := (le_div_iff₀ hn0).mp hre
    nlinarith only [he']
  rw [Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,←Real.exp_add]
  exact Real.exp_le_exp.mpr he

end PhaseNearWeight

lemma wave_modulus_of_normalized_value (e Z : ℂ) (he : e ≠ 0)
    (hZ : ‖e⁻¹*Z-1‖ ≤ 1/2) : ‖e‖/2 ≤ ‖Z‖ := by
  have ht : 1 ≤ ‖e⁻¹*Z‖+‖e⁻¹*Z-1‖ := by
    have hh := norm_sub_le (e⁻¹*Z) (e⁻¹*Z-1)
    simpa only [sub_sub_cancel,norm_one] using hh
  have hh : 1/2 ≤ ‖e⁻¹*Z‖ := by linarith
  have hm := mul_le_mul_of_nonneg_left hh (norm_nonneg e)
  have hn : ‖e‖*‖e⁻¹*Z‖ = ‖Z‖ := by
    rw [←norm_mul,mul_inv_cancel_left₀ he]
  rw [hn] at hm
  simpa only [mul_one_div] using hm

lemma normalized_wave_weight_lower (c n φ R : ℝ) (hc : 0 < c) (hn : 1 ≤ n)
    (hR0 : 0 ≤ R) (hR : R ≤ n^6*Real.exp (n*φ)) (e Z : ℂ)
    (he : e ≠ 0) (heB : c*Real.exp (n*φ) ≤ ‖e‖)
    (hZ : ‖e⁻¹*Z-1‖ ≤ 1/2) :
    c/4*(n^6)⁻¹ ≤ ‖Z‖/(Real.exp (n*φ)+R) := by
  have hn0 : 0 < n := zero_lt_one.trans_le hn
  have hn6 : 1 ≤ n^6 := one_le_pow₀ hn
  have hexp : 0 < Real.exp (n*φ) := Real.exp_pos _
  have hW : 0 < Real.exp (n*φ)+R := add_pos_of_pos_of_nonneg hexp hR0
  have hhalf := wave_modulus_of_normalized_value e Z he hZ
  have hlower : c*Real.exp (n*φ)/2 ≤ ‖Z‖ := by linarith
  have hupper : Real.exp (n*φ)+R ≤ 2*n^6*Real.exp (n*φ) := by
    nlinarith [mul_le_mul_of_nonneg_right hn6 hexp.le]
  apply (le_div_iff₀ hW).mpr
  calc
    _ ≤ (c/4*(n^6)⁻¹)*(2*n^6*Real.exp (n*φ)) :=
      mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = c*Real.exp (n*φ)/2 := by field_simp; ring
    _ ≤ ‖Z‖ := hlower

end YauCounterexamples

end

end OAI
