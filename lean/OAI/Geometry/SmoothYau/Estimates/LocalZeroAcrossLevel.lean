import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.TestAsSmooth

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (K : Compacts E)

lemma exponential_square_integrable (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    Integrable (fun x => Real.exp (2*τ*φ x)*(u x*u x)) (volume : Measure E) := by
  convert testPair_integrable K (testMultiply K (exponentialWeight φ τ) u)
    (testMultiply K (exponentialWeight φ τ) u) using 1
  ext x
  simp only [testMultiply_apply, exponentialWeight_apply]
  rw [show 2*τ*φ x = τ*φ x+τ*φ x by ring, Real.exp_add]
  ring

lemma exponential_square_integral (φ : SmoothScalar E) (τ : ℝ) (u : EllipticTest K) :
    testPair K (testMultiply K (exponentialWeight φ τ) u)
      (testMultiply K (exponentialWeight φ τ) u) =
      ∫ x, Real.exp (2*τ*φ x)*(u x*u x) := by
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [testMultiply_apply, exponentialWeight_apply]
  rw [show 2*τ*φ x = τ*φ x+τ*φ x by ring, Real.exp_add]
  ring

lemma exponential_square_lower (φ : SmoothScalar E) (τ b : ℝ) (hτ : 0 ≤ τ)
    (u : EllipticTest K) :
    Real.exp (2*τ*b) * (∫ x in {x | b < φ x}, u x*u x) ≤
      testPair K (testMultiply K (exponentialWeight φ τ) u)
        (testMultiply K (exponentialWeight φ τ) u) := by
  have hS : MeasurableSet {x | b < φ x} :=
    isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous |>.measurableSet
  rw [exponential_square_integral, ← integral_indicator hS, ← integral_const_mul]
  apply integral_mono (((testPair_integrable K u u).indicator hS).const_mul _)
    (exponential_square_integrable K φ τ u)
  intro x
  dsimp only
  by_cases hx : b < φ x
  · rw [indicator_of_mem (show x ∈ {y : E | b < φ y} from hx)]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx.le (by positivity))) (mul_self_nonneg _)
  · rw [indicator_of_notMem (show x ∉ {y : E | b < φ y} from hx), mul_zero]
    exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)

lemma exponential_square_upper (φ : SmoothScalar E) (τ c : ℝ) (hτ : 0 ≤ τ)
    (r : EllipticTest K) (hr : ∀ x, c < φ x → r x = 0) :
    testPair K (testMultiply K (exponentialWeight φ τ) r)
        (testMultiply K (exponentialWeight φ τ) r) ≤
      Real.exp (2*τ*c) * testPair K r r := by
  rw [exponential_square_integral, testPair, ← integral_const_mul]
  apply integral_mono (exponential_square_integrable K φ τ r)
    ((testPair_integrable K r r).const_mul _)
  intro x
  by_cases hx : c < φ x
  · simp only [hr x hx, mul_zero, le_refl]
  · exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (by positivity)))
      (mul_self_nonneg _)

theorem exponential_support_dominance (φ : SmoothScalar E) (u r : EllipticTest K)
    (C T c : ℝ) (hC : 0 ≤ C)
    (hest : ∀ τ ≥ T,
      testPair K (testMultiply K (exponentialWeight φ τ) u) (testMultiply K (exponentialWeight φ τ) u) ≤
        C * testPair K (testMultiply K (exponentialWeight φ τ) r) (testMultiply K (exponentialWeight φ τ) r))
    (hr : ∀ x, c < φ x → r x = 0) : ∀ x, c < φ x → u x = 0 := by
  intro x hx
  obtain ⟨b,hcb,hbx⟩ := exists_between hx
  let S := {y | b < φ y}
  let J := ∫ y in S, u y*u y
  have hJ : 0 ≤ J := integral_nonneg fun _ => mul_self_nonneg _
  have hbound : ∀ᶠ τ : ℝ in atTop, J ≤
      C * testPair K r r * Real.exp ((2*(c-b))*τ) := by
    filter_upwards [eventually_ge_atTop (max T 0)] with τ hτ
    have ht := (le_max_left ..).trans hτ
    have ht0 := (le_max_right ..).trans hτ
    have hlo := exponential_square_lower K φ τ b ht0 u
    have hup := exponential_square_upper K φ τ c ht0 r hr
    have hh := hlo.trans ((hest τ ht).trans (mul_le_mul_of_nonneg_left hup hC))
    change Real.exp (2*τ*b)*J ≤ C*(Real.exp (2*τ*c)*testPair K r r) at hh
    apply (mul_le_mul_iff_right₀ (Real.exp_pos (2*τ*b))).mp
    refine hh.trans_eq ?_
    rw [show Real.exp (2*τ*c) = Real.exp (2*τ*b)*Real.exp ((2*(c-b))*τ) by
      rw [← Real.exp_add]; congr 1; ring]
    ring
  have hlim : Tendsto (fun τ : ℝ => C*testPair K r r*Real.exp ((2*(c-b))*τ)) atTop (𝓝 0) := by
    have he : Tendsto (fun τ : ℝ => Real.exp ((2*(c-b))*τ)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (by linarith : 2*(c-b) < 0)).mpr tendsto_id)
    simpa only [mul_zero] using he.const_mul (C*testPair K r r)
  have hJ0 : J = 0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim hbound) hJ
  have hae : (fun y => u y*u y) =ᵐ[(volume : Measure E).restrict S] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => mul_self_nonneg _) (testPair_integrable K u u).restrict).mp hJ0
  have hop : IsOpen S := isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous
  have heq := (volume : Measure E).eqOn_open_of_ae_eq hae hop (u.contDiff.continuous.mul u.contDiff.continuous).continuousOn
    continuous_const.continuousOn
  have hh := heq hbx
  simpa using (mul_self_eq_zero.mp hh)


end

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] (e : ι → E)

theorem local_zero_across_level (a : ι → ι → SmoothScalar E)
    (ha : ∀ i j, a i j = a j i) (V ψ u : SmoothScalar E) (x₀ : E)
    (hψ : ψ x₀ = 0) (hpos : Matrix.PosDef (fun i j => a i j x₀))
    (hgrad : (fun i => SmoothScalar.directional (e i) ψ x₀) ≠ 0)
    (O : Set E) (hO : IsOpen O) (hx₀ : x₀ ∈ O)
    (hsol : ∀ x ∈ O, coefficientSchrodinger e a V u x = 0)
    (hzero : ∀ x ∈ O, 0 < ψ x → u x = 0) : (u : E → ℝ) =ᶠ[𝓝 x₀] 0 := by
  let η := tangentPhase ψ x₀
  have hη : η x₀ = 0 := tangentPhase_at ψ x₀ hψ
  have hηgrad : (fun i => SmoothScalar.directional (e i) η x₀) ≠ 0 := by
    simpa only [η, tangentPhase_derivative_center] using hgrad
  obtain ⟨H,hH,U,hU,T,_hT,hcar⟩ := exists_local_weighted_carleman e a ha V η x₀ hη hpos hηgrad
  let φ := convexifyPhase η H
  have hφ₀ : φ x₀ = 0 := by
    change η x₀ + (H/2)*(η x₀*η x₀) = 0
    rw [hη]; ring
  have hsmall : ∀ᶠ x in 𝓝 x₀, -1 < H*η x :=
    ((((continuous_const.mul (SmoothScalar.contDiff η).continuous) :
      Continuous (fun x => H*η x)).tendsto x₀).eventually_const_lt (by change -1 < H*η x₀; rw [hη]; norm_num))
  obtain ⟨R,hR,hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hU (inter_mem (hO.mem_nhds hx₀) hsmall))
  let r := R/2
  have hr : 0 < r := half_pos hR
  let K : Compacts E := ⟨Metric.closedBall x₀ r, isCompact_closedBall x₀ r⟩
  have hK (x : E) (hx : x ∈ K) : x ∈ U ∧ x ∈ O ∧ -1 < H*η x := by
    apply hRsub
    apply lt_of_le_of_lt (show dist x x₀ ≤ r from hx)
    dsimp [r]; linarith
  let χ : ContDiffBump x₀ := ⟨r/2,r, half_pos hr, by linarith⟩
  let w : EllipticTest K := ⟨fun x => χ x * u x, χ.contDiff.mul (SmoothScalar.contDiff u), by
    intro x hx
    have hχ : χ x = 0 := χ.zero_of_le_dist (by
      change ¬ dist x x₀ ≤ r at hx
      exact (lt_of_not_ge hx).le)
    simp only [hχ, zero_mul, Pi.zero_apply]⟩
  have hw (x : E) : w x = χ x * u x := rfl
  let c := -r^2/8
  have hc : c < 0 := by dsimp [c]; nlinarith [sq_pos_of_pos hr]
  have hres : ∀ x, c < φ x → testSchrodinger K e a V w x = 0 := by
    intro x hxphi
    by_cases hxK : x ∈ K
    · have hxO := (hK x hxK).2.1
      by_cases hxi : x ∈ Metric.ball x₀ (r/2)
      · have heq : (w : E → ℝ) =ᶠ[𝓝 x] u := by
          filter_upwards [χ.eventuallyEq_one_of_mem_ball hxi] with y hy
          simp only [hw, Pi.one_apply] at *
          rw [hy, one_mul]
        rw [testSchrodinger_eval_congr K e a V u w x heq]
        exact hsol x hxO
      · have hxψ : 0 < ψ x := by
          by_contra hn
          have hgap := tangentPhase_annular_gap ψ x₀ x r H hr (le_of_not_gt hn)
            (le_of_not_gt hxi) (hK x hxK).2.2
          change φ x ≤ c at hgap
          exact not_lt_of_ge hgap hxphi
        have heq : (w : E → ℝ) =ᶠ[𝓝 x] 0 := by
          filter_upwards [hO.mem_nhds hxO,
            (isOpen_lt continuous_const (SmoothScalar.contDiff ψ).continuous).mem_nhds hxψ] with y hyO hyψ
          simp only [hw, hzero y hyO hyψ, mul_zero, Pi.zero_apply]
        exact testSchrodinger_zero_of_eventually_zero K e a V w x heq
    · exact (testSchrodinger K e a V w).zero_on_compl hxK
  have hupper := exponential_support_dominance K φ w (testSchrodinger K e a V w) 8 T c
    (by norm_num) (fun τ hτ => hcar K (fun x hx => (hK x hx).1) τ hτ w) hres
  filter_upwards [(isOpen_lt continuous_const (SmoothScalar.contDiff φ).continuous).mem_nhds
    (show c < φ x₀ by rw [hφ₀]; exact hc), Metric.ball_mem_nhds x₀ (half_pos hr)] with x hxφ hxb
  have hχ : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hxb)
  have hh := hupper x hxφ
  simpa only [hw, hχ, one_mul, Pi.zero_apply] using hh



end YauCounterexamples
end

end OAI
