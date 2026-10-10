import OAI.Geometry.RCD.Transport.MeasuredTransportSupport
import OAI.Geometry.RCD.Metric.UniformInteriorLimitMass

namespace OAI

/-! # Scale-uniform density tests of the actual value and energy limits -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.uniform_interior_density_energy_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2≤n)
    {S ρ τ R η B : ℝ} (hS : 0<S) (hτ : 0≤τ) (hρτ : ρ<τ)
    (hη : 0≤η) (hroom : τ+2*η<S) (hτR : τ<R) (hRS : R<S) (hηB : η<B) (z : Euclidean n) (hzR : ‖z‖+η<R)
    (p : ℕ → X) (r ε : ℕ → ℝ) (v : ℕ → X → Euclidean n)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (g : Euclidean n → ℝ) (hg : ∀ W<S, ∃ L : ℝ≥0, LipschitzOnWith L g (closedBall 0 W))
    (hconv : ∀ W : ℝ, 0<W → W<S → ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (W*r k)),
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v k x)|≤δ)
    (ν : FiniteMeasure (Euclidean n))
    (henergy : Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
      (closedBall (p k) (R*r k))
      (r k^2/(hausdorff n X).real (ball (p k) (S*r k)))).map (v k)) atTop (𝓝 ν))
    (a b : Euclidean n →ᵇ ℝ) (ha : ∀ y, 0≤a y) (hb : ∀ y, 0≤b y)
    (ha0 : ∀ y, ρ≤‖y‖ → a y=0) (hb0 : ∀ y, ρ≤‖y‖ → b y=0)
    (haz : ∀ y, y∉closedBall z η → a y=0) (hbz : ∀ y, y∉closedBall z η → b y=0)
    (hapos : 0<∫ y, a y ∂(euclideanBallProbability n S : Measure (Euclidean n)))
    (hbpos : 0<∫ y, b y ∂(euclideanBallProbability n S : Measure (Euclidean n))) :
    let α := normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
      (a.integrable _) ha hapos
    let β := normalizedDensityLaw (euclideanBallProbability n S : Measure (Euclidean n))
      (b.integrable _) hb hbpos
    ∃ Q : ProbabilityMeasure (Euclidean n × Euclidean n),
      IsOptimalCoupling (α : Measure (Euclidean n)) (β : Measure (Euclidean n))
        (Q : Measure (Euclidean n × Euclidean n)) ∧
      ((∫ y, g y ∂(β : Measure (Euclidean n)))-(∫ y, g y ∂(α : Measure (Euclidean n))))^2≤
        (∫ y, dist y.1 y.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))*
          (Real.exp ((n:ℝ)*4*η)*max ((∫ y, a y ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖a‖)
            ((∫ y, b y ∂(euclideanBallProbability n S : Measure (Euclidean n)))⁻¹*‖b‖))*
          (ν : Measure (Euclidean n)).real (closedBall z B) := by
  dsimp only
  obtain ⟨D,hn₀,hn₁⟩ := hX.measured_transport_data_nonzero hn hS hτ hρτ p r ε v hr hεlim hv
    a b ha hb ha0 hb0 hapos hbpos
  let W := (τ+S)/2
  have hτS : τ<S := hτR.trans hRS
  have hW : 0<W := by dsimp [W]; linarith
  have hτW : τ<W := by dsimp [W]; linarith
  have hWS : W<S := by dsimp [W]; linarith
  obtain ⟨L,hgL⟩ := hg W hWS
  apply D.limit_uniform_interior_local_mass hn hS hτ hτW hWS.le hτS hη hroom hηB z hzR
    hr hcurv hε hε1 hεlim hv (fun k => w (k+D.offset)) hgL
  · intro δ hδ
    filter_upwards [(tendsto_add_atTop_nat D.offset).eventually (hconv W hW hWS δ hδ)] with k hk
    have hh := (ae_restrict_iff' measurableSet_ball).mp hk
    exact hh.mono fun x hx hdist => hx
      (hdist.trans_lt (mul_lt_mul_of_pos_right hτW (hr (k+D.offset))))
  · intro k
    exact (hn₀ k).mono fun x hx => not_not.mp (fun hh => hx (haz _ hh))
  · intro k
    exact (hn₁ k).mono fun x hx => not_not.mp (fun hh => hx (hbz _ hh))
  · exact henergy.comp (tendsto_add_atTop_nat D.offset)

end RegularPointCoordinates

end

end OAI
