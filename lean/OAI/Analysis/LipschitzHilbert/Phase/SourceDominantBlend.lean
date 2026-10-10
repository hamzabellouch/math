import OAI.Analysis.LipschitzHilbert.Phase.SourceDominantPrediction

namespace OAI

/-! The dominant branch of the actual source comparison. Raw amplitude
motion and complementary-mass coefficient motion feed the proved logarithmic
comparison; the residual error is absorbed by the prescribed blend. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_dominant_prediction_comparison
    {n n' p μ ε K C q u θ : ℝ} (hn : 0 < n) (hn' : 0 < n')
    (hp : 0 < p) (hμ : 0 ≤ μ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hpower : n^μ ≤ K) (hsize : C*n^μ ≤ K)
    (c c' : ι → ℝ) (hc : ∀ i, 0 < c i) (hc' : ∀ i, 0 < c' i)
    (i₀ : ι) (hcn : c i₀ ≤ n)
    (hmass : ∑ i : RemainderIndex i₀, c i/n ≤ u)
    (f : ι → κ → ℝ) (b : ℝ)
    (A A' : ι → EuclideanSpace ℂ κ) (lam lam' : ι → ℂ)
    (hlam : ∀ i, ‖lam i‖ ≤ 1) (hpath : lam i₀ ≠ 0)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hqε : q ≤ ε)
    (hphase : ‖lam' i₀-lam i₀‖ ≤ q*‖lam i₀‖)
    (hA : ∀ i, ‖A i‖ ≤ C*c i)
    (hscaled : ∀ i,
      ‖massPowerScale n' (c' i) (-(1/p)) (μ-1+1/p) • A' i-
        diagonalModulation (f i)
          (massPowerScale n (c i) (-(1/p)) (μ-1+1/p) • A i) b‖ ≤
        ε*(c i/n)^(1/p)*(c i)^μ)
    (hmove : ∀ i,
      ‖((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i)-
        ((n^(μ-1):ℝ):ℂ) • (lam i • diagonalModulation (f i) (A i) b)‖ ≤
        ε*K*(c i/n))
    (hC0 : 0 ≤ (c i₀/n)^(1-μ-1/p)*‖lam i₀‖)
    (hC1 : (c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 1)
    (hdrop : 1-(c i₀/n)^(1-μ-1/p)*‖lam i₀‖ ≤ 2*u)
    (hcmove : |(c' i₀/n')^(1-μ-1/p)*‖lam' i₀‖-
      (c i₀/n)^(1-μ-1/p)*‖lam i₀‖| ≤ 24*ε*u)
    (hp4 : 4 ≤ p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hsmall : Real.exp (24*p*ε*(2*K)) ≤ 2)
    (habsorb : 2*24*p*ε*(2*K) ≤ θ) :
    let U := diagonalModulationIsometry (fun k => -f i₀ k) b
    let Y := (c i₀/n)^(1/p) • ((c i₀)^(μ-1) • A i₀)
    let Y' := (c' i₀/n')^(1/p) • U ((c' i₀)^(μ-1) • A' i₀)
    let R := ∑ i : RemainderIndex i₀,
      (c i/n)*‖(c i)^(μ-1) • radialShrink (2*ε*c i) (A i)‖^p
    let R' := ∑ i : RemainderIndex i₀, (c' i/n')*‖(c' i)^(μ-1) • A' i‖^p
    let Z := (scalarPhase (lam i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n^(μ-1):ℝ):ℂ) •
        (lam i • diagonalModulation (f i) (radialShrink (2*ε*c i) (A i)) b))
    let Z' := (scalarPhase (lam' i₀))⁻¹ • U
      (∑ i : RemainderIndex i₀, ((n'^(μ-1):ℝ):ℂ) • (lam' i • A' i))
    let cp := (c i₀/n)^(1-μ-1/p)*‖lam i₀‖
    let cp' := (c' i₀/n')^(1-μ-1/p)*‖lam' i₀‖
    energyRatio p (1+‖Y'‖^p+R') (cp' • Y'+Z') ≤
      Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*energyRatio p (1+‖Y‖^p+R) (cp • Y+Z)+θ) := by
  dsimp only
  have hK0 : 0 ≤ K := by linarith
  have hs0 : 0 ≤ ∑ i : RemainderIndex i₀, c i/n :=
    Finset.sum_nonneg (fun i _ => (div_pos (hc i) hn).le)
  have hu : 0 ≤ u := hs0.trans hmass
  obtain ⟨hY,hY',hYm,hR,hZm,hZ⟩ := source_dominant_coordinate_control hn hn' hp hμ
    hε0 hε1 hK0 hC hpower hsize c c' hc hc' i₀ hcn hmass f b A A' lam lam'
    hlam hpath hq0 hq1 hqε hphase hA hscaled hmove
  apply dominant_prediction_blended_domination hp4 (by norm_num : (1:ℝ) ≤ 24)
    (show 1 ≤ 2*K by linarith) hε0 hu hC0 hC1 _ hR _ _ _ _ _ hY' _ _ _ _ _ hsmall hθ0 hθ1 habsorb
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (div_pos (hc i) hn).le
      (Real.rpow_nonneg (norm_nonneg _) _))
  · exact hY.trans (by linarith)
  · exact hdrop.trans (by nlinarith)
  · exact hZ.trans (by nlinarith)
  · exact hYm.trans (by nlinarith [mul_nonneg hε0 hK0])
  · exact hcmove
  · exact hZm.trans (by nlinarith [mul_nonneg (mul_nonneg hε0 hK0) hu])

end LipschitzHilbert

end

end OAI
