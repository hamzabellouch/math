import OAI.Geometry.IsometricImmersion.Caps.FiniteCapInduction

namespace OAI

noncomputable section
open Set Filter Function MeasureTheory
open scoped ContDiff Topology BigOperators ENNReal NNReal

namespace SmoothLocal.Flow
open SmoothLocal.Geometry SmoothLocal.ODE SmoothLocal.Weighted SmoothLocal.Model
open SmoothLocal.HighEquation SmoothLocal.Analytic SmoothLocal.Sobolev

def lowerCapPointwiseRequests {bStar : ℝ} (n : ℕ) (r : LowerCapRectangle bStar) :
    List (ℕ × LowerCapRectangle bStar) := lowerCapMetricRequests (n-6) r.expand

theorem lowerCapPointwiseRequests_length {bStar : ℝ} (n : ℕ)
    (r : LowerCapRectangle bStar) :
    (lowerCapPointwiseRequests n r).length = 2*(n-6) :=
  lowerCapMetricRequests_length (n-6) r.expand

theorem lowerCapPointwiseRequests_full_order_le {bStar : ℝ} (n : ℕ)
    (r : LowerCapRectangle bStar) (b : ℕ × LowerCapRectangle bStar)
    (hb : b ∈ lowerCapPointwiseRequests n r) {k : ℕ} (hk : k ≤ b.1+2) :
    k ≤ max 8 (n+3) := by
  by_cases hn : n ≤ 6
  · have hn0 : n-6=0 := Nat.sub_eq_zero_of_le hn
    simp [lowerCapPointwiseRequests,hn0,lowerCapMetricRequests] at hb
  · have h := lowerCapMetricRequests_full_order_le (n-6) r.expand b hb hk
    omega

theorem uniform_finite_varying_lowerCap_pointwise
    (G Z d c e0 kappa : ℝ) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hd : 0 < d) (hc : 0 < c)
    {bStar : ℝ} (J : CapMetricJetBudget bStar) (n : ℕ) (r : LowerCapRectangle bStar)
    (hJ : ∀ b ∈ lowerCapPointwiseRequests n r, 0 ≤ J b.1 b.2) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (g : MetricField) (U : Set Coord) (z : Coord → ℝ) (Y : ℝ → ℝ → ℝ) (W : Set Coord),
        SmoothPositiveOn g U → IsOpen U → modelSquare ⊆ U →
        (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
          ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) →
        (∀ p ∈ modelSquare, d ≤ |(g p).det|) →
        CapInductionHeight g U Z c e0 z → CapInductionFlow g U G Z d c e0 kappa z Y W →
        FiniteCapMetricJets g Y J (lowerCapPointwiseRequests n r) →
        CoordinateBound z (r.image Y) n B := by
  obtain ⟨H,hH⟩ := uniform_finite_varying_lowerCap_L2 G Z d c e0 kappa hG hZ hd hc
    J (n-6) r.expand hJ
  let M := heightQuotientJetBound G Z d c
  let B := (squareSobolevWeight (flowInteriorRadius M r.margin r.margin)+1)*(H : ℝ)
  have hr := flowInteriorRadius_pos M r.margin_pos r.margin_pos
  have hB : 0 ≤ B := by
    dsimp only [B,squareSobolevWeight]
    positivity
  refine ⟨B,hB,?_⟩
  intro g U z Y W hg hU hSU hgB hdet hh hf hlocal
  exact CapInductionFlow.pointwise_from_larger_L2 hh hf hG hZ hd hc r
    ((hH g U z Y W hg hU hSU hgB hdet hh hf hlocal).mono
      (by omega : n+2 ≤ (n-6)+8) le_rfl)

theorem coordinateL2Bound_of_pointwise_in_modelSquare
    {z : Coord → ℝ} {V : Set Coord} {n : ℕ} {B : ℝ}
    (hV : MeasurableSet V) (hVS : V ⊆ modelSquare) (hB : 0 ≤ B)
    (hbound : CoordinateBound z V n B) :
    CoordinateL2Bound z V n (originalC8L2Budget B) := by
  intro ds hds
  rw [originalC8L2Budget_coe]
  exact (bounded_real_eLpNorm_two hV hB (fun p hp => by
    rw [Real.norm_eq_abs]
    exact hbound ds hds p hp)).trans
      (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (z := 1/(2 : ℝ))
        (measure_mono hVS) (by norm_num)))

end SmoothLocal.Flow

end

end OAI
