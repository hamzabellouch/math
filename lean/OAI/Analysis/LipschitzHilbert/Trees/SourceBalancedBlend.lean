import OAI.Analysis.LipschitzHilbert.Phase.SourceDominantPrediction

namespace OAI

/-! The balanced source prediction after blending with one. All denominator
and numerator bounds are obtained from the actual finite child data. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics

/-- A denominator at least one leaves the same logarithmic numerator bound. -/
theorem source_energyRatio_log_upper {E : Type*} [NormedAddCommGroup E]
    {p d K : ℝ} (hp : 1 ≤ p) (hd : 1 ≤ d) {x : E} (hx : ‖x‖ ≤ K) :
    Real.log (energyRatio p d x) ≤ p*K := by
  have hd0 : 0 < d := zero_lt_one.trans_le hd
  have hzero : energyRatio p d (0:E) ≤ 1 := by
    rw [energyRatio,norm_zero,Real.zero_rpow (by linarith : p ≠ 0),add_zero]
    exact (div_le_one hd0).mpr hd
  have hzlog : Real.log (energyRatio p d (0:E)) ≤ 0 :=
    Real.log_nonpos (energyRatio_pos hd0 (0:E)).le hzero
  have hlog := (abs_le.mp (log_energyRatio_lipschitz hp hd0 x (0:E))).2
  simp only [sub_zero] at hlog
  have hb := mul_le_mul_of_nonneg_left hx (by linarith : 0 ≤ p)
  linarith

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_balanced_prediction_blend
    {n n' p μ ε K u C θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (hp : 1 ≤ p) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hpower : n^μ ≤ K)
    (hu : 1/2 ≤ u) (hsum : ∑ i, c i/n ≤ 1)
    (frequency : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (frequency i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hnumerator : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (frequency i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC : 0 ≤ C) (hsize : C*n^μ ≤ K) (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let X := fun i => (c i)^(μ-1) • radialShrink (2*ε*c i) (A i)
    let X' := fun i => (c' i)^(μ-1) • A' i
    let actual := energyRatio p (1+∑ i, (c' i/n')*‖X' i‖^p)
      (∑ i, ((((c' i/n')^(1-μ):ℝ):ℂ) • (lam' i • X' i)))
    let model := energyRatio p (1+∑ i, (c i/n)*‖X i‖^p)
      (∑ i, ((((c i/n)^(1-μ):ℝ):ℂ) •
        (lam i • diagonalModulation (frequency i) (X i) b)))
    actual ≤ Real.exp ((6*p*ε*K+2*θ*(p*K))*u)*((1-θ)*model+θ) := by
  dsimp only
  have hcomparison := source_balanced_prediction_comparison hn hn' c c' hc hc' hp hε hK hpower
    hu hsum frequency b A A' lam lam' hlam hscaled hnumerator
  dsimp only at hcomparison
  have hterm (i : ι) :
      ‖(((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
        ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ ≤ K*(c i/n) := by
    rw [source_normalized_modulated_numerator_eq hn (hc i)]
    have ha : ‖diagonalModulation (frequency i) (radialShrink (2*ε*c i) (A i)) b‖ ≤ C*c i := by
      rw [norm_diagonalModulation]
      exact (norm_radialShrink_le (mul_nonneg (mul_nonneg (by norm_num) hε) (hc i).le) _).trans (hA i)
    exact (source_numerator_term_bound hn (hc i) hC _ _ ha (hlam i)).trans
      (mul_le_mul_of_nonneg_right hsize (div_pos (hc i) hn).le)
  have hnorm : ‖∑ i, (((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
      ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ ≤ K := by
    calc
      _ ≤ ∑ i, ‖(((c i/n)^(1-μ):ℝ):ℂ) • (lam i • diagonalModulation (frequency i)
        ((c i)^(μ-1) • radialShrink (2*ε*c i) (A i)) b)‖ := norm_sum_le _ _
      _ ≤ ∑ i, K*(c i/n) := Finset.sum_le_sum fun i _ => hterm i
      _ = K*(∑ i, c i/n) := (Finset.mul_sum ..).symm
      _ ≤ K*1 := mul_le_mul_of_nonneg_left hsum hK
      _ = K := mul_one K
  have hd : 1 ≤ 1+∑ i, (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_pos (hc i) hn).le (Real.rpow_nonneg (norm_nonneg _) _))
  have hd' : 1 ≤ 1+∑ i, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ =>
      mul_nonneg (div_pos (hc' i) hn').le (Real.rpow_nonneg (norm_nonneg _) _))
  exact balanced_blended_prediction_domination
    (energyRatio_pos (zero_lt_one.trans_le hd') _)
    (energyRatio_pos (zero_lt_one.trans_le hd) _) hθ0 hθ1 (mul_nonneg (by linarith) hK) hu
    hcomparison.1 (source_energyRatio_log_upper hp hd hnorm)

end LipschitzHilbert

end

end OAI
