import OAI.Geometry.RCD.Sobolev.CompactTestHarmonicLimits
import OAI.Geometry.RCD.Harmonic.HarmonicBoundaryLayer

namespace OAI

/-! # The same compactness subsequence retains the boundary-layer estimate -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem CompactHarmonicBoundaryLimit.difference_converges {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X}
    {p : ℕ → X} {r : ℕ → ℝ} {V : ℕ → X → Euclidean n} {S R : ℝ} {ψ : Euclidean n → ℝ}
    (d : CompactHarmonicBoundaryLimit hX p r V S R ψ)
    (hr : ∀ k, 0<r k) (hRS : R≤S) :
    ∀ W : ℝ, 0<W → W<R → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (d.subsequence k+d.shift)) (W*r (d.subsequence k+d.shift))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic
          (d.target (d.subsequence k)-d.boundary (d.subsequence k)) x-
          (d.value (V (d.subsequence k+d.shift) x)-ψ (V (d.subsequence k+d.shift) x))|≤δ := by
  intro W hW hWR δ hδ
  filter_upwards [d.convergence W hW hWR (δ/2) (half_pos hδ),
    d.strictMono.tendsto_atTop.eventually (d.recovery (δ/2) (half_pos hδ))] with k hk hrec
  have hsub : ball (p (d.subsequence k+d.shift)) (W*r (d.subsequence k+d.shift))⊆
      ball (p (d.subsequence k+d.shift)) (S*r (d.subsequence k+d.shift)) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (hWR.le.trans hRS) (hr _).le)
  have he : SobolevSpace.toLp (hausdorff n X) hX.quadratic
      (d.target (d.subsequence k)-d.boundary (d.subsequence k))=ᵐ[hausdorff n X]
      fun x => SobolevSpace.toLp (hausdorff n X) hX.quadratic (d.target (d.subsequence k)) x-
        SobolevSpace.toLp (hausdorff n X) hX.quadratic (d.boundary (d.subsequence k)) x := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hk,ae_restrict_of_ae_restrict_of_subset hsub hrec,ae_restrict_of_ae he] with x hx hy hex
  rw [hex]
  rcases abs_le.mp hx with ⟨hx₀,hx₁⟩
  rcases abs_le.mp hy with ⟨hy₀,hy₁⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem CompactHarmonicBoundaryLimit.boundary_layer {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n} {S R : ℝ} {ψ : Euclidean n → ℝ}
    (d : CompactHarmonicBoundaryLimit hX p r V S R ψ)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*(S*r k)^2)
    (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k)) :
    ∃ A : ℝ, 0<A ∧ ∀ δ : ℝ, 0<δ → 4*δ≤R → R+2*δ≤S → ∀ᶠ k in atTop,
      ((hausdorff n X).real (ball (p (d.subsequence k+d.shift)) (S*r (d.subsequence k+d.shift))))⁻¹*
        (∫ z in closedBall (p (d.subsequence k+d.shift)) (R*r (d.subsequence k+d.shift)) \
          ball (p (d.subsequence k+d.shift)) ((R-δ)*r (d.subsequence k+d.shift)),
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic
            (d.target (d.subsequence k)-d.boundary (d.subsequence k)) z)^2 ∂hausdorff n X)≤A*δ^2 := by
  obtain ⟨C,hC,hbound⟩ := hX.harmonic_replacement_boundary_layer hn
  have hE := d.energy_nonneg
  refine ⟨C*d.energyConstant+1,by positivity,?_⟩
  intro δ hδ hR hS
  have hlim := (hεlim.comp (tendsto_add_atTop_nat d.shift)).comp d.strictMono.tendsto_atTop
  filter_upwards [hlim.eventually (Iio_mem_nhds (show 0<δ/8 by positivity))] with k hk
  have hh := hbound (p (d.subsequence k+d.shift)) (r (d.subsequence k+d.shift)) S R δ
    (ε (d.subsequence k+d.shift)) (hr _) hδ hR hS (hε _) hk.le (V _)
    (hV _).metric (hcurv _) (d.boundary (d.subsequence k)) (d.target (d.subsequence k))
    (d.dirichlet _) (d.harmonic _) d.energyConstant (d.boundary_energy _)
  exact hh.trans (by nlinarith [sq_nonneg δ])

end RegularPointCoordinates

end

end OAI
