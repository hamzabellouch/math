import OAI.Geometry.RCD.Sobolev.CompactTestHarmonicReplacements
import OAI.Geometry.RCD.Harmonic.InnerHarmonicLimit

namespace OAI

/-! # Actual recovered boundary data and their classical harmonic limits -/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

structure CompactHarmonicBoundaryLimit {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (p : ℕ → X) (r : ℕ → ℝ) (V : ℕ → X → Euclidean n) (S R : ℝ) (ψ : Euclidean n → ℝ) where
  shift : ℕ
  boundary : ℕ → SobolevSpace (hausdorff n X) hX.quadratic
  target : ℕ → SobolevSpace (hausdorff n X) hX.quadratic
  energyConstant : ℝ
  energy_nonneg : 0≤energyConstant
  dirichlet : ∀ k, target k-boundary k∈SobolevSpace.dirichlet (hausdorff n X) hX.quadratic
    (ball (p (k+shift)) (R*r (k+shift)))
  harmonic : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic
    (ball (p (k+shift)) (R*r (k+shift))) (target k)
  boundary_energy : ∀ k, r (k+shift)^2*energyForm (hausdorff n X) hX.quadratic (boundary k) (boundary k)≤
    energyConstant*(hausdorff n X).real (ball (p (k+shift)) (S*r (k+shift)))
  recovery : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
    ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (k+shift)) (S*r (k+shift))),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (boundary k) x-ψ (V (k+shift) x)|≤δ
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  value : Euclidean n → ℝ
  measurable : Measurable value
  continuous : ContinuousOn value (ball 0 R)
  weak : EuclideanWeakHarmonicOn value R
  smooth : ContDiffOn ℝ ∞ value (ball 0 R)
  localLipschitz : ∀ W<R, ∃ L : ℝ≥0, LipschitzOnWith L value (closedBall 0 W)
  convergence : ∀ W : ℝ, 0<W → W<R → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
    ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (subsequence k+shift)) (W*r (subsequence k+shift))),
      |SobolevSpace.toLp (hausdorff n X) hX.quadratic (target (subsequence k)) x-
        value (V (subsequence k+shift) x)|≤δ

theorem NoncollapsedRCD.compact_test_harmonic_limits {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hcurvR : ∀ k, -1≤K*(2*(R*r k))^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    {ψ : Euclidean n → ℝ} (hψ : InteriorSmoothTest n S ψ) :
    Nonempty (CompactHarmonicBoundaryLimit hX p r V S R ψ) := by
  obtain ⟨C,E,hC,hE,N,u,w,hw,hu⟩ := hX.compact_test_harmonic_replacements hn hS hR hRS
    p r ε V hr hcurv hcurvR hε hε1 hεlim hV hψ
  obtain ⟨a,ha,g,hgm,hgc,hgw,hgs,hgL,hconv⟩ := hX.inner_harmonic_limit hn hS hR
    (by linarith) hC (fun k => p (k+N)) (fun k => r (k+N)) (fun k => ε (k+N))
    (fun k => V (k+N)) (fun k => hr (k+N)) (fun k => hcurv (k+N))
    (fun k => hε (k+N)) (hεlim.comp (tendsto_add_atTop_nat N)) (fun k => hV (k+N))
    w (fun k => (hw k).2.1) (fun k => (hw k).2.2.2.1)
  exact ⟨{ shift := N
           boundary := u
           target := w
           energyConstant := E
           energy_nonneg := hE
           dirichlet := fun k => (hw k).1
           harmonic := fun k => (hw k).2.1
           boundary_energy := fun k => (hw k).2.2.2.2.2
           recovery := hu
           subsequence := a
           strictMono := ha
           value := g
           measurable := hgm
           continuous := hgc
           weak := hgw
           smooth := hgs
           localLipschitz := hgL
           convergence := hconv }⟩

end RegularPointCoordinates

end

end OAI
