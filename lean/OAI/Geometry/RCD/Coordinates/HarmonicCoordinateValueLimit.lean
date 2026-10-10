import OAI.Geometry.RCD.Harmonic.HarmonicBoundaryIdentification
import OAI.Geometry.RCD.Coordinates.EuclideanCoordinateTests
import OAI.Geometry.RCD.Harmonic.PointedRadialDistance

namespace OAI

/-! # Actual harmonic coordinate replacements have the prescribed value limit -/

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem CompactHarmonicBoundaryLimit.convergence_of_eqOn {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X}
    {p : ℕ → X} {r ε : ℕ → ℝ} {V : ℕ → X → Euclidean n} {S R : ℝ} {ψ : Euclidean n → ℝ}
    (d : CompactHarmonicBoundaryLimit hX p r V S R ψ)
    (hRS : R≤S) (hr : ∀ k, 0<r k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    {f : Euclidean n → ℝ} (he : EqOn d.value f (ball 0 R))
    {W : ℝ} (hW : 0<W) (hWR : W<R) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p (d.subsequence k+d.shift)) (W*r (d.subsequence k+d.shift))),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (d.target (d.subsequence k)) x-
          f (V (d.subsequence k+d.shift) x)|≤δ := by
  let a := fun k => d.subsequence k+d.shift
  have hta : Tendsto a atTop atTop := (tendsto_add_atTop_nat d.shift).comp d.strictMono.tendsto_atTop
  have heps : ∀ᶠ k in atTop, ε (a k)<(R-W)/2 :=
    (hεlim.comp hta).eventually (eventually_lt_nhds (by linarith))
  filter_upwards [d.convergence W hW hWR δ hδ,heps] with k hk hεk
  filter_upwards [hk,self_mem_ae_restrict measurableSet_ball] with x hx hxb
  have hnorm := (abs_le.mp (pointed_radial_distance (hr (a k))
    (hW.le.trans (hWR.le.trans hRS)) (hV (a k)).metric
    (hxb.le.trans (mul_le_mul_of_nonneg_right (hWR.le.trans hRS) (hr _).le)))).2
  have hdist : dist x (p (a k))/r (a k)<W := (div_lt_iff₀ (hr _)).mpr hxb
  have hin : V (a k) x∈ball (0:Euclidean n) R := by
    simp only [mem_ball,dist_zero_right]
    linarith
  have he' : d.value (V (d.subsequence k+d.shift) x)=
      f (V (d.subsequence k+d.shift) x) := he hin
  simpa only [he'] using hx

theorem NoncollapsedRCD.harmonic_coordinate_value_limit {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) {S R : ℝ}
    (hS : 0<S) (hR : 0<R) (hRS : 2*R≤S)
    (p : ℕ → X) (r ε : ℕ → ℝ) (V : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hcurvR : ∀ k, -1≤K*(2*(R*r k))^2) (hcurvS : ∀ k, -1≤K*(S*r k)^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hV : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (V k))
    (i : Fin n) :
    ∃ ψ : Euclidean n → ℝ, InteriorSmoothTest n S ψ ∧
      ∃ d : CompactHarmonicBoundaryLimit hX p r V S R ψ,
        EqOn d.value (fun z => z i) (ball 0 R) ∧
        ∀ W : ℝ, 0<W → W<R → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
          ∀ᵐ x ∂(hausdorff n X).restrict
            (ball (p (d.subsequence k+d.shift)) (W*r (d.subsequence k+d.shift))),
            |SobolevSpace.toLp (hausdorff n X) hX.quadratic (d.target (d.subsequence k)) x-
              V (d.subsequence k+d.shift) x i|≤δ := by
  have hRS' : R<S := by linarith
  obtain ⟨ψ,hψ,hcoord,_,hψh⟩ := compact_euclidean_coordinate_test hR hRS' i
  obtain ⟨d⟩ := hX.compact_test_harmonic_limits hn hS hR hRS p r ε V hr hcurv hcurvR
    hε hε1 hεlim hV hψ
  have he := d.eq_harmonic_boundary hn hS hR hRS' hr hcurvS hε hεlim hV hψ hψh
  have hec : EqOn d.value (fun z => z i) (ball 0 R) :=
    fun z hz => (he hz).trans (hcoord (ball_subset_closedBall hz))
  exact ⟨ψ,hψ,d,hec,fun _ hW hWR _ hδ => d.convergence_of_eqOn
    hRS'.le hr hεlim hV hec hW hWR hδ⟩

end RegularPointCoordinates

end

end OAI
