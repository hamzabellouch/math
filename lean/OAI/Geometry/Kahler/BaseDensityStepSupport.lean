import OAI.Geometry.Kahler.BaseCentralSecond

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

def phaseSphere (z : Circle) (ξ : Sphere) : Sphere :=
  ⟨(z:ℂ) • (ξ:Base),by simp only [Metric.mem_sphere,dist_zero_right,norm_smul,z.norm_coe,sphere_norm,one_mul]⟩

lemma densityBandwidth_le_twice {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) :
    densityBandwidth Q j ≤ 2*Q^j := by
  cases j with
  | zero => simp [densityBandwidth]
  | succ j =>
    rw [densityBandwidth_succ]
    have hh := densityBandwidth_lt hQ j
    omega

lemma phase_second_from_steps {Q n N : ℕ} (hQ : 2 ≤ Q)
    {c K : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hK : 0 ≤ K) (hN : 2/c ≤ (2:ℝ)^N)
    (W : ℕ → Base → ℝ) (hzero : W 0=fun _ => 1)
    (hsm : ∀ j ≤ n, ContDiff ℝ ∞ (W j))
    (hpos : ∀ j ≤ n, ∀ ξ : Sphere, 0 < W j ξ)
    (hder : ∀ j ≤ n, ∀ ξ : Sphere, |phaseDerivative (W j) ξ| ≤ K*(Q:ℝ)^j*W j ξ)
    (hstep : ∀ j, j < n → ∀ ξ : Sphere, c*W j ξ ≤ W (j+1) ξ ∧ W (j+1) ξ ≤ 2*W j ξ)
    (hband : PhaseBandwidth (W n) (densityBandwidth Q n)) (ξ : Sphere) :
    |phaseDerivative (phaseDerivative (W n)) ξ| ≤
      (2*(Real.exp K*(2/c))*4^N*Real.exp 2)*((Q:ℝ)^n)^2*W n ξ := by
  let A := Real.exp K*(2/c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ0 : (0:ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hg : ∀ u : ℝ, W n ((Circle.exp u:ℂ) • (ξ:Base)) ≤ A*(1+(Q:ℝ)^n*|u|)^N*W n ξ := by
    intro u
    let V : ℕ → ℝ → ℝ := fun j θ => W j ((Circle.exp θ:ℂ) • (ξ:Base))
    have hv0 : V 0=fun _ => 1 := by funext θ; simp [V,hzero]
    have hvd : ∀ j ≤ n, ∀ θ, HasDerivAt (V j) (phaseDerivative (W j) ((Circle.exp θ:ℂ) • (ξ:Base))) θ :=
      fun j hj θ => phaseDerivative_curve ((hsm j hj).differentiable (by simp)) ξ θ
    have hvder : ∀ j ≤ n, ∀ θ, |deriv (V j) θ| ≤ K*(Q:ℝ)^j*V j θ := by
      intro j hj θ
      rw [(hvd j hj θ).deriv]
      exact hder j hj (phaseSphere (Circle.exp θ) ξ)
    have hh := orbit_growth_nat hQ hc hc1 hK hN V hv0
      (fun j hj θ => hpos j hj (phaseSphere (Circle.exp θ) ξ))
      (fun j hj θ => (hvd j hj θ).differentiableAt) hvder
      (fun j hj θ => hstep j hj (phaseSphere (Circle.exp θ) ξ)) 0 u
    simp only [V,zero_add,Circle.exp_zero,Circle.coe_one,one_smul] at hh
    refine hh.trans ?_
    apply mul_le_mul_of_nonneg_right _ (hpos n le_rfl ξ).le
    apply mul_le_mul_of_nonneg_left _ hA
    apply pow_le_pow_left₀ (by positivity)
    exact max_le (by linarith [mul_nonneg (pow_nonneg hQ0.le n) (abs_nonneg u)]) (by linarith : (Q:ℝ)^n*|u| ≤ 1+(Q:ℝ)^n*|u|)
  exact phase_second_weighted (hsm n le_rfl) hband (pow_pos hQ0 n) hA
    (by exact_mod_cast densityBandwidth_le_twice hQ n) N ξ
    (fun z => hpos n le_rfl (phaseSphere z ξ)) hg

end PinchedHartogs.BaseConstruction

end

end OAI
