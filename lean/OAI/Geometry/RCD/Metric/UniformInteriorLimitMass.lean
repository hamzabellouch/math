import OAI.Geometry.RCD.Metric.UniformInteriorLocalMass
import OAI.Geometry.RCD.Transport.MeasuredTransportValues
import OAI.Geometry.RCD.Metric.MeasuredEndpointLimit
import OAI.Geometry.RCD.Metric.FiniteMeasureClosedBound

namespace OAI

/-! # Scale-uniform local testing of the actual limiting energy measure -/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.limit_uniform_interior_local_mass {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {S τ W R η B : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτW : τ<W) (hWS : W≤S)
    (hτS : τ<S) (hη : 0≤η) (hroom : τ+2*η<S) (hηB : η<B) (z : Euclidean n)
    (hzR : ‖z‖+η<R)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2)
    (hε : ∀ k, 0≤ε k) (hε1 : ∀ k, ε k≤1) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    {g : Euclidean n → ℝ} {L : ℝ≥0} (hg : LipschitzOnWith L g (closedBall 0 W))
    (hclose : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂hausdorff n X,
      dist x (p (k+D.offset))≤τ*r (k+D.offset) →
        |SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) x-g (v (k+D.offset) x)|≤δ)
    (hz0 : ∀ k, ∀ᵐ x ∂(D.left k : Measure X), v (k+D.offset) x∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ x ∂(D.right k : Measure X), v (k+D.offset) x∈closedBall z η)
    (ν : FiniteMeasure (Euclidean n))
    (henergy : Tendsto (fun k => (localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
      (closedBall (p (k+D.offset)) (R*r (k+D.offset)))
      (r (k+D.offset)^2/(hausdorff n X).real (ball (p (k+D.offset)) (S*r (k+D.offset))))).map
      (v (k+D.offset))) atTop (𝓝 ν)) :
    ∃ Q : ProbabilityMeasure (Euclidean n × Euclidean n),
      IsOptimalCoupling (α : Measure (Euclidean n)) (β : Measure (Euclidean n))
        (Q : Measure (Euclidean n × Euclidean n)) ∧
      ((∫ y, g y ∂(β : Measure (Euclidean n)))-(∫ y, g y ∂(α : Measure (Euclidean n))))^2≤
        (∫ y, dist y.1 y.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))*(Real.exp ((n:ℝ)*4*η)*c₀)*
          (ν : Measure (Euclidean n)).real (closedBall z B) := by
  obtain ⟨Q,t,ht,hopt,_,hcost⟩ := D.extract_endpoint_limit hn hS hτ hτS hr hε hε1 hεlim hv
  refine ⟨Q,hopt,?_⟩
  have hmean := D.mean_difference_tendsto hS hτ hτW hWS hr hεlim hv w hg hclose
  have harg : Tendsto (fun k => (n:ℝ)*2*(2*η+ε (k+D.offset))) atTop (𝓝 ((n:ℝ)*4*η)) := by
    convert ((hεlim.comp (tendsto_add_atTop_nat D.offset)).const_add (2*η)).const_mul ((n:ℝ)*2) using 1 <;> ring_nf
    funext k
    simp only [Function.comp_def,Nat.add_comm]
  have hcap := ((Real.continuous_exp.tendsto _).comp harg).mul D.control_limit
  have hbound := D.uniform_interior_local_image_mass hn hS hτ hτS hη hroom hηB z hzR
    hr hcurv hε hεlim hv w hz0 hz1
  have hδ (δ : ℝ) (hδ : 0<δ) :
      ((∫ y, g y ∂(β : Measure (Euclidean n)))-(∫ y, g y ∂(α : Measure (Euclidean n))))^2≤
        (∫ y, dist y.1 y.2^2 ∂(Q : Measure (Euclidean n × Euclidean n)))*(Real.exp ((n:ℝ)*4*η)*c₀)*
          ((ν : Measure (Euclidean n)).real (closedBall z B)+δ) := by
    have he := finite_measure_closed_eventual_bound henergy (A := closedBall z B) isClosed_closedBall hδ
    apply le_of_tendsto_of_tendsto ((hmean.comp ht.tendsto_atTop).pow 2)
      ((hcost.mul (hcap.comp ht.tendsto_atTop)).mul_const _)
    filter_upwards [ht.tendsto_atTop.eventually hbound,ht.tendsto_atTop.eventually he] with k hk he
    apply hk.trans
    exact mul_le_mul_of_nonneg_left he (mul_nonneg
      (integral_nonneg fun _ => sq_nonneg _)
      (mul_nonneg (Real.exp_nonneg _) (D.control_nonneg (t k))))
  have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add
    ((ν : Measure (Euclidean n)).real (closedBall z B))
  have hlim' := hlim.const_mul ((∫ y, dist y.1 y.2^2
    ∂(Q : Measure (Euclidean n × Euclidean n)))*(Real.exp ((n:ℝ)*4*η)*c₀))
  simp only [add_zero] at hlim'
  apply ge_of_tendsto hlim'
  exact Eventually.of_forall fun k => hδ (1/((k:ℝ)+1)) (by positivity)

end RegularPointCoordinates

end

end OAI
