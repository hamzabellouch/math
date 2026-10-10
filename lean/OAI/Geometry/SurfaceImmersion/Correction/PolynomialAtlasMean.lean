import OAI.Geometry.SurfaceImmersion.Correction.TensorAtlasMeanExplicit
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialMeanTransport

namespace OAI

/-! The atlas mean estimate with its read and restore constants exposed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

local instance polynomialAtlasMeanFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialAtlasMeanFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialAtlasMeanDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialAtlasMeanDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialAtlasMeanSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAtlasMeanSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem atlasMean_polynomial_majorants
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (L : ℕ) (p : ℕ → ℕ) (c G : ℕ → ℝ)
    (hc : ∀ m, 1 ≤ c m) (hG : ∀ m, 1 ≤ G m)
    (D E : ℕ → ℝ) (hD : ∀ m, 1 ≤ D m) (hE : ∀ m, 0 ≤ E m)
    (hd : ∀ m (i : A.centers) (f : Base → A.centers → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ s m C f →
      WeightedBound univ s m (D m*C) (A.tensorPlaneRead i (A.tensorDecode f)))
    (he : ∀ m (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (E m*C) (A.tensorPlaneRestore f)) :
    ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧
      ∀ {s : ℝ}, 0 < s → s ≤ 1 → ∀ η : ℝ, 0 < η →
      ∀ μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor,
      (∀ i f, ContDiff ℝ ∞ f → InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        ContDiff ℝ ∞ (μ i f)) →
      (∀ i m C f, 1 ≤ C → ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        WeightedBound univ s (m+L) C f → WeightedBound univ s m (η * polynomialMeanProfile p c G m C) (μ i f)) →
      (∀ i m C D f g, 1 ≤ C → 0 ≤ D → ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) f →
        InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r) g →
        WeightedBound univ s (m+L) C f → WeightedBound univ s (m+L) C g →
        WeightedBound univ s (m+L) D (f-g) →
        WeightedBound univ s m (polynomialMeanProfile p c G m C * η * D) (μ i f - μ i g)) →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator (A.atlasMean μ)))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+c m)
          (transportedMeanGeometry L G D E))
        (polynomialMeanProfile (fun m => 2*p m+2) (fun m => 1+c m)
          (transportedMeanGeometry L G D E)) := by
  have hB (m : ℕ) (C : ℝ) (_hC : 1 ≤ C) : 1 ≤ polynomialMeanProfile p c G m C := by
    apply one_le_mul_of_one_le_of_one_le (hc m)
    apply one_le_pow₀
    exact (hG m).trans (le_add_of_nonneg_right (zero_le_one.trans (le_max_left 1 C)))
  intro r hr
  obtain ⟨hball,β,κ,hβ,hκ,hm⟩ := A.atlasMean_majorants_explicit reference href L
    (polynomialMeanProfile p c G) (polynomialMeanProfile p c G) hB hB D E hD hE hd he r hr
  subst β κ
  refine ⟨hball,?_⟩
  intro s hs hs1 η hη μ hsm hv hdiff
  apply (hm hs hs1 η hη μ hsm hv hdiff).mono_majorants
  · intro m C hC
    simpa only [polynomialMeanProfile, transportedMeanGeometry] using
      polynomialMeanProfile_value_transport_bound (p m) (zero_le_one.trans (hc m))
        (hG m) (hD (m+L)) (hE m) hC
  · intro m C hC
    simpa only [polynomialMeanProfile, transportedMeanGeometry] using
      polynomialMeanProfile_transport_bound (p m) (zero_le_one.trans (hc m))
        (hG m) (hD (m+L)) (hE m) hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
