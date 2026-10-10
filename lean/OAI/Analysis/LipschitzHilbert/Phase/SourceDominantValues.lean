import OAI.Analysis.LipschitzHilbert.Phase.SourceDominantBlend
import OAI.Analysis.LipschitzHilbert.Trees.SourcePathValues

namespace OAI

/-! The dominant comparison for the original source ratio, with the exact
coordinate changes discharged by the path identities. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem source_dominant_values_blend
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
    let shrink := fun i => if i = i₀ then A i else radialShrink (2*ε*c i) (A i)
    sourcePredictionValue p μ n' c' A' lam' ≤
      Real.exp ((12*24^2*p^2*(2*K)^2*ε+θ*(p*(2*K)))*u)*
        ((1-θ)*sourceSnapshotPrediction p μ n c shrink lam f b+θ) := by
  dsimp only
  have hlam' : lam' i₀ ≠ 0 := (scalarPhase_relative_motion hpath hq1 hphase).1
  rw [source_prediction_path_value hn' hp c' hc' A' lam' i₀ hlam'
    (diagonalModulationIsometry (fun k => -f i₀ k) b),
    source_snapshot_path_value hn hp c hc A lam i₀ hpath f b]
  exact source_dominant_prediction_comparison hn hn' hp hμ hε0 hε1 hK hC hpower hsize
    c c' hc hc' i₀ hcn hmass f b A A' lam lam' hlam hpath hq0 hq1 hqε hphase hA
    hscaled hmove hC0 hC1 hdrop hcmove hp4 hθ0 hθ1 hsmall habsorb

end LipschitzHilbert

end

end OAI
