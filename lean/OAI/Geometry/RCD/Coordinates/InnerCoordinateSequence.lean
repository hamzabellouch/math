import OAI.Geometry.RCD.Coordinates.CoordinateTargetNorm
import OAI.Geometry.RCD.Harmonic.FirstOrderLocalization

namespace OAI

/-! # A normalized actual harmonic coordinate sequence on one common inner ball -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.inner_coordinate_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) {S R T : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S) (hT : 0<T) (hTR : T<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hcurvR : ∀ k, -1≤K*(2*(R*r k))^2) (hcurvS : ∀ k, -1≤K*(S*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (i : Fin n) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∃ w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p (a k)) (r (a k)) T
        (1/((k:ℝ)+1)) (V (a k))) ∧
      (∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
        (ball (p (a k)) (T*r (a k))) (w k)) ∧
      (∀ k, harmonicTargetNorm hX (p (a k)) (T*r (a k)) (w k)≤T+2) ∧
      ∀ W : ℝ, 0<W → W<T → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
        ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (a k)) (W*r (a k))),
          |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-V (a k) x i|≤δ := by
  obtain ⟨ψ,_,d,_,hc⟩ := hX.harmonic_coordinate_value_limit hn hS hR hRS p r ε V hr
    hcurv hcurvR hcurvS hε hε1 hεlim hV i
  let a₀ := fun k => d.subsequence k+d.shift
  have ha₀ : StrictMono a₀ := fun _ _ hij => Nat.add_lt_add_right (d.strictMono hij) d.shift
  have hTS : T≤S := by linarith
  have hnorm := hX.coordinate_target_norm_eventually hT hTS (p∘a₀) (r∘a₀) (ε∘a₀) (V∘a₀)
    (fun k => hr (a₀ k)) (hεlim.comp ha₀.tendsto_atTop) (fun k => hV (a₀ k))
    (fun k => d.target (d.subsequence k)) i (hc T hT hTR 1 zero_lt_one)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hnorm
  let a₁ := fun k => a₀ (k+N)
  have hadd : StrictMono (fun k : ℕ => k+N) := fun _ _ hij => Nat.add_lt_add_right hij N
  have ha₁ : StrictMono a₁ := ha₀.comp hadd
  obtain ⟨b,hb,hbV⟩ := inner_measured_subsequence hS hT hTS
    (p:=p∘a₁) (r:=r∘a₁) (ε:=ε∘a₁) (V:=V∘a₁) (η:=fun k => 1/((k:ℝ)+1))
    (fun k => hr (a₁ k)) (fun k => hε (a₁ k)) (fun k => hV (a₁ k))
    (fun _ => (hX.finiteOnBounded _ isBounded_ball).ne)
    (fun k => ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr (a₁ k)))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne)
    (hεlim.comp ha₁.tendsto_atTop) (fun k => by positivity)
  refine ⟨a₁∘b,ha₁.comp hb,(fun k => d.target (d.subsequence (b k+N))),hbV,?_,?_,?_⟩
  · intro k
    exact (d.harmonic (d.subsequence (b k+N))).mono (hausdorff n X) hX.quadratic
      (ball_subset_ball (mul_le_mul_of_nonneg_right hTR.le (hr _).le))
  · intro k
    exact hN (b k+N) (Nat.le_add_left N (b k))
  · intro W hW hWT δ hδ
    exact (hadd.comp hb).tendsto_atTop.eventually (hc W hW (hWT.trans hTR) δ hδ)

end RegularPointCoordinates

end

end OAI
