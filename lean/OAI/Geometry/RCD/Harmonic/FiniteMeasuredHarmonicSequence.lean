import OAI.Geometry.RCD.Harmonic.FiniteHarmonicSubsequence

namespace OAI

/-! # The whole coordinate family on one measured inner sequence -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.finite_measured_harmonic_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0 < r k) (hcurv : ∀ k, -1≤K*(16*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) 16 (ε k) (V k)) :
    ∃ α : ℕ → ℕ, StrictMono α ∧ ∃ w : Fin n → ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p (α k)) (r (α k)) 5
        (1/((k:ℝ)+1)) (V (α k))) ∧
      (∀ i k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p (α k)) (5*r (α k))) (w i k)) ∧
      (∀ i k, harmonicTargetNorm hX (p (α k)) (5*r (α k)) (w i k)≤7) ∧
      (∀ i W, 0<W → W<5 → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (α k)) (W*r (α k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w i k) x-V (α k) x i|≤δ) := by
  obtain ⟨a,ha,w,hw,hnorm,hconv⟩ := hX.finite_harmonic_coordinate_sequence hn
    p r ε V hr hcurv hε hε1 hεlim hV
  obtain ⟨b,hb,hbV⟩ := inner_measured_subsequence
    (S:=16) (R:=5) (by norm_num) (by norm_num) (by norm_num)
    (p:=p∘a) (r:=r∘a) (ε:=ε∘a) (V:=V∘a) (η:=fun k => 1/((k:ℝ)+1))
    (fun k => hr (a k)) (fun k => hε (a k)) (fun k => hV (a k))
    (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr (a k)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (hεlim.comp ha.tendsto_atTop) (fun k => by positivity)
  refine ⟨a∘b,ha.comp hb,(fun i k => w i (b k)),hbV,?_,?_,?_⟩
  · exact fun i k => hw i (b k)
  · exact fun i k => hnorm i (b k)
  · intro i W hW hW5 δ hδ
    exact hb.tendsto_atTop.eventually (hconv i W hW hW5 δ hδ)

end RegularPointCoordinates

end

end OAI
