import Mathlib
import OAI.Geometry.SmoothYau.Geometry.AnnularRelativeMargin
import OAI.Geometry.SmoothYau.Limits.CompactExteriorBackgroundDomination

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

lemma roundPower_centered_derivative_square (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) :
    ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖^2 =
      (n:ℝ)^2*(Complex.normSq (planarLinear a b p)^(n-1)-(roundPower a b n p)^2) := by
  have he : fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0 =
      innerSL ℝ (sphereCoordinates p (ambientPowerGradient a b n p)) := by
    ext v
    rw [roundPower_chart_directional,sphereFrame_inner]
    simp only [innerSL_apply_apply,real_inner_comm]
  rw [he,innerSL_apply_norm,←real_inner_self_eq_norm_sq,sphereCoordinates_inner,
    ambientPowerGradient_norm_sq _ _ _ _ ha hb hab,ambientPowerGradient_radial _ _ _ hn]
  simp only [roundPower]
  ring

theorem roundPower_centered_jet_lower (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) :
    ‖planarLinear a b p‖^n ≤ |roundPower a b n p|+
      ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hr : Complex.normSq (planarLinear a b p) ≤ 1 := by
    have horth : inner ℝ b a=0 := (real_inner_comm a b).trans hab
    let x : Euclidean (d+1) := p
    have hs := real_inner_self_nonneg (x := x - (inner ℝ a x • a + inner ℝ b x • b))
    have hx : inner ℝ x x=1 := by
      rw [real_inner_self_eq_norm_sq]
      have hp : ‖(p : Euclidean (d+1))‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
      dsimp [x]; rw [hp]; norm_num
    simp only [inner_sub_left,inner_sub_right,inner_add_left,inner_add_right,
      inner_smul_left,inner_smul_right,ha,hb,hab,horth,hx,mul_one,mul_zero,add_zero,
      zero_add,conj_trivial] at hs
    have hre : (planarLinear a b p).re = inner ℝ a x := by simp [planarLinear_apply,x]
    have him : (planarLinear a b p).im = inner ℝ b x := by simp [planarLinear_apply,x]
    rw [Complex.normSq_apply,hre,him]
    rw [real_inner_comm a x,real_inner_comm b x] at hs
    nlinarith
  have hR0 := Complex.normSq_nonneg (planarLinear a b p)
  have hp : Complex.normSq (planarLinear a b p)^n ≤ Complex.normSq (planarLinear a b p)^(n-1) := by
    calc
      _ = Complex.normSq (planarLinear a b p)^(n-1)*Complex.normSq (planarLinear a b p) := by
        rw [←pow_succ,Nat.sub_add_cancel hn]
      _ ≤ _ := mul_le_of_le_one_right (pow_nonneg hR0 _) hr
  have hsq := roundPower_centered_derivative_square a b n hn ha hb hab p
  have he : (‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ))^2 =
      Complex.normSq (planarLinear a b p)^(n-1)-(roundPower a b n p)^2 := by
    rw [div_pow,hsq]; field_simp
  have heN : (‖planarLinear a b p‖^n)^2 = Complex.normSq (planarLinear a b p)^n := by
    rw [←pow_mul, Nat.mul_comm n 2, pow_mul,Complex.sq_norm]
  have hw := abs_nonneg (roundPower a b n p)
  have hv : 0 ≤ ‖fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by positivity
  have hrn : 0 ≤ ‖planarLinear a b p‖^n := pow_nonneg (norm_nonneg _) _
  have hw2 := sq_abs (roundPower a b n p)
  nlinarith [mul_nonneg hw hv]

theorem roundPower_dominant_perturbation_jet_lower (a b : Euclidean (d+1)) (n : ℕ)
    (hn : 1 ≤ n) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) (p : Sphere d) (v : Sphere d → ℝ)
    (hv : ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ v)
    (t C : ℝ) (hnC : 2*C ≤ (n:ℝ)^2)
    (hdom : (n:ℝ)^6*Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n)
    (hsmall : |v p|+‖fderiv ℝ (v ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) ≤
      C*(n:ℝ)^4*Real.exp ((n:ℝ)*t)) :
    (Real.exp ((n:ℝ)*t)+‖planarLinear a b p‖^n)/4 ≤
      |roundPower a b n p+v p|+
      ‖fderiv ℝ ((roundPower a b n+v) ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := zero_lt_one.trans_le hn1
  have hhalf : C*(n:ℝ)^4*Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n/2 := by
    have hh := mul_le_mul_of_nonneg_right hnC
      (show 0 ≤ (n:ℝ)^4*Real.exp ((n:ℝ)*t) by positivity)
    have he : (n:ℝ)^2*((n:ℝ)^4*Real.exp ((n:ℝ)*t)) =
        (n:ℝ)^6*Real.exp ((n:ℝ)*t) := by ring
    rw [he] at hh
    nlinarith
  have hex : Real.exp ((n:ℝ)*t) ≤ ‖planarLinear a b p‖^n := by
    calc
      _ ≤ (n:ℝ)^6*Real.exp ((n:ℝ)*t) := le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hn1)
      _ ≤ _ := hdom
  have hlower := roundPower_centered_jet_lower a b n hn ha hb hab p
  have habs : |roundPower a b n p| ≤ |roundPower a b n p+v p|+|v p| := by
    simpa only [Real.norm_eq_abs, add_neg_cancel_right,abs_neg] using norm_add_le (roundPower a b n p+v p) (-v p)
  have hzero : (0 : Euclidean d) ∈ (chartAt (Euclidean d) p).target := by
    rw [sphere_chart_target]; trivial
  have hD₁ := (contDiffAt_inChart (roundPower_smooth a b n) p hzero).differentiableAt (by simp)
  have hD₂ := (contDiffAt_inChart hv p hzero).differentiableAt (by simp)
  have heq : ((roundPower a b n+v) ∘ (chartAt (Euclidean d) p).symm) =
      (roundPower a b n ∘ (chartAt (Euclidean d) p).symm)+(v ∘ (chartAt (Euclidean d) p).symm) := rfl
  rw [heq,fderiv_add hD₁ hD₂]
  let A := fderiv ℝ (roundPower a b n ∘ (chartAt (Euclidean d) p).symm) 0
  let B := fderiv ℝ (v ∘ (chartAt (Euclidean d) p).symm) 0
  have hd : ‖A‖ ≤ ‖A+B‖+‖B‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (A+B) B
  have hdiv := div_le_div_of_nonneg_right hd hn0.le
  rw [add_div] at hdiv
  change (Real.exp ((n:ℝ)*t)+‖planarLinear a b p‖^n)/4 ≤
    |roundPower a b n p+v p|+‖A+B‖/(n:ℝ)
  change ‖planarLinear a b p‖^n ≤ |roundPower a b n p|+‖A‖/(n:ℝ) at hlower
  change |v p|+‖B‖/(n:ℝ) ≤ _ at hsmall
  linarith

end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function
open scoped Topology ContDiff Manifold InnerProductSpace
variable {d : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (d+1)) = d+1) := ⟨by simp [Euclidean]⟩

theorem roundPower_exterior_perturbation_jet_lower
    (a b : Euclidean (d+1)) (ha : inner ℝ a a=1) (hb : inner ℝ b b=1)
    (hab : inner ℝ a b=0) {K : Set (Sphere d)} (hK : IsCompact K)
    (φ : Sphere d → ℝ) (hφ : ContinuousOn φ K)
    (hr : ∀ p ∈ K, 0 < ‖planarLinear a b p‖)
    (hgap : ∀ p ∈ K, φ p < Real.log ‖planarLinear a b p‖)
    (v : ℕ → Sphere d → ℝ)
    (hv : ∀ n, ContMDiff 𝓘(ℝ,Euclidean d) 𝓘(ℝ,ℝ) ∞ (v n))
    (C : ℝ)
    (hsmall : ∀ n ≥ 2, ∀ p ∈ K,
      |v n p|+‖fderiv ℝ (v n ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) ≤
        C*(n:ℝ)^4*Real.exp ((n:ℝ)*φ p)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ K,
      (Real.exp ((n:ℝ)*φ p)+‖planarLinear a b p‖^n)/4 ≤
        |roundPower a b n p+v n p|+
        ‖fderiv ℝ ((roundPower a b n+v n) ∘ (chartAt (Euclidean d) p).symm) 0‖/(n:ℝ) := by
  have hcont : ContinuousOn (fun p : Sphere d => ‖planarLinear a b p‖) K :=
    ((planarLinear a b).continuous.comp continuous_subtype_val).norm.continuousOn
  filter_upwards [compact_exterior_background_domination hK hcont hφ hr hgap 6,
    eventually_ge_atTop (Nat.ceil (max 1 (2*C))),eventually_ge_atTop 2] with n hdom hlarge hn2
  intro p hp
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnC : 2*C ≤ (n:ℝ) := calc
    _ ≤ max 1 (2*C) := le_max_right _ _
    _ ≤ (Nat.ceil (max 1 (2*C)) : ℝ) := Nat.le_ceil _
    _ ≤ n := by exact_mod_cast hlarge
  exact roundPower_dominant_perturbation_jet_lower a b n (by omega) ha hb hab p
    (v n) (hv n) (φ p) C (by nlinarith) (hdom p hp).le (hsmall n hn2 p hp)


end YauCounterexamples
end

end OAI
