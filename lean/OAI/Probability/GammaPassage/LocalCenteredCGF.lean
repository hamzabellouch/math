import OAI.Probability.GammaPassage.LocalPassageMGF
import OAI.Probability.GammaPassage.MGFDerivative
import OAI.Probability.GammaPassage.DyadicDerivativeBound

namespace OAI

namespace GammaFPP.FiniteLocal
open MeasureTheory ProbabilityTheory PlanarFPP Real Filter Topology

/-- Derivative at zero from the actual positive moment at rate/2. -/
theorem finitePassageTime_hasDerivAt_cgf_zero {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) :
    HasDerivAt (cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate))
      (∫ v, finitePassageTime p q R v ∂finiteGammaMeasure shape rate) 0 := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let : IsProbabilityMeasure (finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate) := by
    unfold finiteGammaMeasure
    infer_instance
  apply hasDerivAt_cgf_zero_of_nonneg_exp (measurable_finitePassageTime p q R hR)
    (c := rate/2) ?_ (by linarith)
    (integrable_finitePassageTime_exp hs hr p q R hR (rate/2) le_rfl)
  filter_upwards [finiteGammaMeasure_ae_nonneg (ι := ↥(localEdges p q R)) hs hr] with v hv
  exact finitePassageTime_nonneg p q R hR v hv

/-- Signed centered cgf estimate, with all smallness conditions explicit. -/
theorem finitePassageTime_cgf_centered {shape rate : ℝ}
    (hs : 0 < shape) (hr : 0 < rate) (p q : Vertex) (R : ℕ)
    (hR : latticeDistance p q < R) (a : ℝ) (ha : |a| ≤ rate/4)
    (hq : (16*(2 : ℝ)^shape/rate^2)*a^2*R ≤ 1/2) :
    cgf (finitePassageTime p q R) (finiteGammaMeasure shape rate) a ≤
      a*(∫ v, finitePassageTime p q R v ∂finiteGammaMeasure shape rate) +
      4*((16*(2 : ℝ)^shape/rate^2)*a^2*R) := by
  let : IsProbabilityMeasure (gammaMeasure shape rate) := isProbabilityMeasure_gammaMeasure hs hr
  let P := finiteGammaMeasure (ι := ↥(localEdges p q R)) shape rate
  let : IsProbabilityMeasure P := by dsimp [P, finiteGammaMeasure]; infer_instance
  let F := finitePassageTime p q R
  let B : ℝ := 16*(2 : ℝ)^shape/rate^2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd : HasDerivAt (cgf F P) (∫ v, F v ∂P) 0 :=
    finitePassageTime_hasDerivAt_cgf_zero hs hr p q R hR
  have hb := dyadic_derivative_bound (cgf F P) a (∫ v, F v ∂P) (2*(B*a^2*R))
    (by positivity) (cgf_zero (X := F) (μ := P)) hd (fun n => ?_)
  · convert hb using 1; ring
  have hn0 : 0 ≤ (1/2 : ℝ)^n := by positivity
  have hn1 : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have han : |a*(1/2 : ℝ)^n| ≤ rate/4 := by
    rw [abs_mul, abs_of_nonneg hn0]
    calc
      _ ≤ |a| *1 := mul_le_mul_of_nonneg_left hn1 (abs_nonneg a)
      _ ≤ _ := by simpa using ha
  have hqn : B*(a*(1/2 : ℝ)^n)^2*R ≤ 1/2 := by
    have hsquare : ((1/2 : ℝ)^n)^2 ≤ 1 := by nlinarith
    calc
      _ = (B*a^2*R)*((1/2 : ℝ)^n)^2 := by ring
      _ ≤ (B*a^2*R)*1 := mul_le_mul_of_nonneg_left hsquare (by positivity)
      _ ≤ _ := by simpa only [mul_one] using hq
  have hrec := finitePassageTime_cgf_recursion hs hr p q R hR
    (a*(1/2 : ℝ)^n) han hqn
  have he : a*(1/2 : ℝ)^n/2 = a*(1/2 : ℝ)^(n+1) := by rw [pow_succ]; ring
  rw [he] at hrec
  convert hrec using 1; ring

end GammaFPP.FiniteLocal

end OAI
