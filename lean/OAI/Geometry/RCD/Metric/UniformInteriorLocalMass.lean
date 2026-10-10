import OAI.Geometry.RCD.Transport.MeasuredTransportData
import OAI.Geometry.RCD.Transport.PointedGeodesicBall
import OAI.Geometry.RCD.Transport.UniformEndpointCompression
import OAI.Geometry.RCD.Coordinates.NormalizedPlanLocalMass
import OAI.Geometry.RCD.Transport.PointedLocalPlanSupport

namespace OAI

/-! # Scale-uniform transport bounds by a localized image-energy mass -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem MeasuredTransportData.uniform_interior_local_image_mass {K : ℝ} {n : ℕ}
    {hX : NoncollapsedRCD K n X} (hn : 2≤n)
    {p : ℕ → X} {r ε : ℕ → ℝ} {S τ R η B : ℝ} {v : ℕ → X → Euclidean n}
    {α β : ProbabilityMeasure (Euclidean n)} {c₀ : ℝ}
    (D : MeasuredTransportData hX p r S τ v α β c₀)
    (hS : 0<S) (hτ : 0≤τ) (hτS : τ<S) (hη : 0≤η) (hroom : τ+2*η<S) (hηB : η<B) (z : Euclidean n)
    (hzR : ‖z‖+η<R)
    (hr : ∀ k, 0<r k) (hcurv : ∀ k, -1≤K*r k^2) (hε : ∀ k, 0≤ε k) (hεlim : Tendsto ε atTop (𝓝 0))
    (hv : ∀ k, IsMeasuredEuclideanApproximation (hausdorff n X) n (p k) (r k) S (ε k) (v k))
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hz0 : ∀ k, ∀ᵐ x ∂(D.left k : Measure X), v (k+D.offset) x∈closedBall z η)
    (hz1 : ∀ k, ∀ᵐ x ∂(D.right k : Measure X), v (k+D.offset) x∈closedBall z η) :
    ∀ᶠ k in atTop,
      ((∫ γ : C(Time,X), SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) (γ 1)
          ∂(D.plan k : Measure C(Time,X)))-
        (∫ γ : C(Time,X), SobolevSpace.toLp (hausdorff n X) hX.quadratic (w k) (γ 0)
          ∂(D.plan k : Measure C(Time,X))))^2≤
      (∫ γ : C(Time,X), (dist (γ 0) (γ 1)/r (k+D.offset))^2 ∂(D.plan k : Measure C(Time,X)))*
        (Real.exp ((n:ℝ)*2*(2*η+ε (k+D.offset)))*D.control k)*
        ((localEnergyMeasure (hausdorff n X) hX.quadratic (w k)
          (closedBall (p (k+D.offset)) (R*r (k+D.offset)))
          (r (k+D.offset)^2/(hausdorff n X).real (ball (p (k+D.offset)) (S*r (k+D.offset))))).map
          (v (k+D.offset)) : Measure (Euclidean n)).real (closedBall z B) := by
  let μ := hausdorff n X
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hend (k : ℕ) := optimalPlan_endpoints (D.left k : Measure X) (D.right k : Measure X)
    (D.plan k : Measure C(Time,X)) (D.optimal k)
  have h0 (k : ℕ) : ∀ᵐ γ ∂(D.plan k : Measure C(Time,X)), dist (γ 0) (p (k+D.offset))≤τ*r (k+D.offset) :=
    ae_of_ae_map (measurable_path_eval 0).aemeasurable ((hend k).1.symm ▸ D.left_support k)
  have h1 (k : ℕ) : ∀ᵐ γ ∂(D.plan k : Measure C(Time,X)), dist (γ 1) (p (k+D.offset))≤τ*r (k+D.offset) :=
    ae_of_ae_map (measurable_path_eval 1).aemeasurable ((hend k).2.symm ▸ D.right_support k)
  have himage := pointed_local_plan_support hτ hτS hroom hηB z hzR
    (fun k => p (k+D.offset)) (fun k => r (k+D.offset)) (fun k => ε (k+D.offset))
    (fun k => v (k+D.offset)) (fun k => hr (k+D.offset)) (fun k => hε (k+D.offset))
    (hεlim.comp (tendsto_add_atTop_nat D.offset)) (fun k => (hv (k+D.offset)).metric)
    D.plan D.geodesic h0 h1
    (fun k => ae_of_ae_map (measurable_path_eval 0).aemeasurable ((hend k).1.symm ▸ hz0 k))
    (fun k => ae_of_ae_map (measurable_path_eval 1).aemeasurable ((hend k).2.symm ▸ hz1 k))
  filter_upwards [himage] with k hk
  have hstay (t : Time) : ∀ᵐ x ∂(D.plan k : Measure C(Time,X)).map (fun γ => γ t),
      x∈v (k+D.offset) ⁻¹' closedBall z B∩closedBall (p (k+D.offset)) (R*r (k+D.offset)) := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable
      (((hv (k+D.offset)).measurable measurableSet_closedBall).inter measurableSet_closedBall)).mpr
    filter_upwards [hk] with γ hγ
    exact ⟨(hγ t).2,(hγ t).1⟩
  have hdist : MemLp (fun γ : C(Time,X) => dist (γ 0) (γ 1)) 2 (D.plan k : Measure C(Time,X)) := by
    apply MemLp.of_bound ((continuous_eval_const 0).dist (continuous_eval_const 1)).aestronglyMeasurable
      (2*τ*r (k+D.offset))
    filter_upwards [h0 k,h1 k] with γ hγ0 hγ1
    rw [Real.norm_eq_abs,abs_of_nonneg dist_nonneg]
    have hh := dist_triangle (γ 0) (p (k+D.offset)) (γ 1)
    rw [dist_comm (p (k+D.offset)) (γ 1)] at hh
    linarith
  have hcomp := D.uniform_endpoint_compression hn hS hτ hτS.le hη hr hcurv hε hv z hz0 hz1 k
  exact (w k).normalized_plan_local_mass μ hX.quadratic (D.plan k) (D.geodesic k)
    (hr (k+D.offset)) (mul_nonneg (Real.exp_nonneg _) (D.control_nonneg k))
    (ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos hS (hr _))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne) hcomp hdist
    (closedBall (p (k+D.offset)) (R*r (k+D.offset)))
    (hv (k+D.offset)).measurable measurableSet_closedBall hstay

end RegularPointCoordinates

end

end OAI
