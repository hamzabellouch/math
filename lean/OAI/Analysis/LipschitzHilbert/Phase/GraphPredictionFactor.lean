import OAI.Analysis.LipschitzHilbert.Trees.FixedPathAverage
import OAI.Analysis.LipschitzHilbert.Phase.PredictionCells

namespace OAI

/-!
# A constructed step factor for the graph prediction

For the fixed snapshot model of §9, combine graph selection, carrier removal,
probability-mixture transfer, finite-cell supremums, and exact normalization.
The resulting factor is an actual measurable step function of average at most
one. Every loss in its comparison retains the off-path mass parameter `u`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert

open PhaseCombinatorics

variable {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]

attribute [local instance] Classical.propDecidable

def predictionCoefficients (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (D p : ℝ) (i : ι) : EuclideanSpace ℂ κ :=
  (((l i ^ (1 - phaseMu D p) : ℝ) : ℂ) * lambda i) • X i

def graphPredictionValue (frequency : ι → κ → ℝ) (l : ι → ℝ)
    (X : ι → EuclideanSpace ℂ κ) (lambda : ι → ℂ) (D p t : ℝ) : ℝ :=
  energyRatio p (1 + ∑ i, l i * ‖X i‖ ^ p)
    (diagonalFourierSum frequency (predictionCoefficients l X lambda D p) t)

omit [Fintype ι] [Fintype κ] [Fintype σ] in
theorem positive_blend {θ x : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hx : 0 < x) :
    0 < (1 - θ) * x + θ := by
  by_cases hθ : θ = 1
  · simp [hθ]
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (sub_pos.mpr (lt_of_le_of_ne hθ1 hθ)) hx) hθ0

/-- The finite-snapshot graph prediction admits a measurable normalized step
factor, with only a relative off-path-mass loss in its pointwise comparison. -/
theorem graph_prediction_step_factor
    (G : ι → ι → Prop) (hG : ∀ ⦃i j⦄, G i j → G j i)
    (w m : ι → ℝ) (hw : ∀ i, 0 < w i)
    (hm : ∀ i, orderMass w (closedNeighborhood G i) ≤ m i)
    (ω τ : Measure ℝ) [IsProbabilityMeasure ω] [IsProbabilityMeasure τ]
    (frequency : ι → κ → ℝ) (l : ι → ℝ) (X : ι → EuclideanSpace ℂ κ)
    (lambda : ι → ℂ) (i₀ : ι) (I : Set ℝ) (P : ℝ → σ)
    {η gap D p K u L H θ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hgap : 0 < gap)
    (hν : FourierGap (predictionMixture ω τ η) gap) (hD : 1 ≤ D) (hp : 4 ≤ p)
    (hfrequency : ∀ i j, i ≠ j → ¬G i j → ∀ k, gap ≤ |frequency i k - frequency j k|)
    (hcard : ∀ S : Finset ι, (S : Set ι).Pairwise (fun i j => ¬G i j) → (S.card : ℝ) ≤ D)
    (hl : ∀ i, 0 ≤ l i) (htotal : ∑ i, l i ≤ 1)
    (hlambda : ∀ i, ‖lambda i‖ ≤ (w i / m i) ^ phaseMu D p)
    (hK : 0 ≤ K) (hu : 0 ≤ u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hmass : (∑ i : RemainderIndex i₀, ‖predictionCoefficients l X lambda D p i‖) ≤ K * u)
    (hfrequencyBound : ∀ i : RemainderIndex i₀, ∀ j, |frequency i j - frequency i₀ j| ≤ L)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : ∀ i, MeasurableSet {t | P t = i}) (hsupport : ∀ᵐ t ∂ω, t ∈ I)
    (hdiameter : ∀ s ∈ I, ∀ t ∈ I, P t = P s → |t - s| ≤ H) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧ Integrable Γ ω ∧ (∀ t, 0 ≤ Γ t) ∧
      (∫ t, Γ t ∂ω) ≤ 1 ∧ (∀ s t, P s = P t → Γ s = Γ t) ∧
      ∀ t ∈ I, (1 - θ) * graphPredictionValue frequency l X lambda D p t + θ ≤
        Real.exp (((η / (1 - η) * (2 * p * K)) + p * L * K * H) * u) * Γ t := by
  let a := predictionCoefficients l X lambda D p
  let denominator := 1 + ∑ i, l i * ‖X i‖ ^ p
  let β := graphPredictionValue frequency l X lambda D p
  let B := fun t => (1 - θ) * β t + θ
  have hp1 : 1 ≤ p := by linarith
  have hd : 0 < denominator := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun i _ => mul_nonneg (hl i) (Real.rpow_nonneg (norm_nonneg _) _))
  have hβpos (t : ℝ) : 0 < β t := energyRatio_pos hd _
  have hβint : Integrable β ω := integrable_diagonal_energyRatio ω frequency a (by linarith) denominator
  have hBint : Integrable B ω := (hβint.const_mul _).add (integrable_const θ)
  have hβaverage : (∫ t, β t ∂ω) ≤ 1 + (η / (1 - η) * (2 * p * K)) * u := by
    have h := graph_prediction_uniform_average G hG w m hw hm ω τ frequency l X lambda i₀
      hη0 hη1 hgap hν hD hp hfrequency hcard hl htotal hlambda (mul_nonneg hK hu) hmass
    change (∫ t, β t ∂ω) ≤ 1 + η / (1 - η) * (2 * p * (K * u)) at h
    simpa only [mul_assoc] using h
  have herror : 0 ≤ η / (1 - η) * (2 * p * K) := by positivity
  have hBaverage : (∫ t, B t ∂ω) ≤ 1 + (η / (1 - η) * (2 * p * K)) * u := by
    dsimp only [B]
    rw [integral_add (hβint.const_mul _) (integrable_const _), integral_const_mul]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have hmul := mul_le_mul_of_nonneg_left hβaverage (sub_nonneg.mpr hθ1)
    have hnonneg := mul_nonneg herror hu
    have hdrop := mul_nonneg hθ0 hnonneg
    nlinarith
  have hcarrier (t : ℝ) : β t = energyRatio p denominator
      (a i₀ + diagonalFourierSum (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) t) :=
    diagonal_carrier_energyRatio frequency a i₀ p denominator t
  have hosc : ∀ s ∈ I, ∀ t ∈ I, P t = P s →
      |Real.log (B t) - Real.log (B s)| ≤ (p * L * K * H) * u := by
    intro s hs t ht hst
    have hb := blend_log_contraction hθ0 hθ1 (hβpos t) (hβpos s)
    have hlog : |Real.log (β t) - Real.log (β s)| ≤
        p * L * (∑ i : RemainderIndex i₀, ‖a i‖) * |t - s| := by
      rw [hcarrier t, hcarrier s]
      exact fixed_path_diagonal_log_motion (diagonalRemainderFrequency frequency i₀)
        (fun i : RemainderIndex i₀ => a i) (a i₀) hL hp1 hd hfrequencyBound s t
    refine hb.trans (hlog.trans ?_)
    calc
      _ ≤ p * L * (∑ i : RemainderIndex i₀, ‖a i‖) * H :=
        mul_le_mul_of_nonneg_left (hdiameter s hs t ht hst) (by positivity)
      _ ≤ p * L * (K * u) * H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) hH
      _ = _ := by ring
  exact exists_normalized_prediction_steps ω B I P hP hsupport
    (fun t _ => positive_blend hθ0 hθ1 (hβpos t)) hBint herror (by positivity) hu hBaverage hosc

end LipschitzHilbert

end

end OAI
