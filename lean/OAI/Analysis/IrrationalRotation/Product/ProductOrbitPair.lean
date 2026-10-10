import OAI.Analysis.IrrationalRotation.Analysis.RepresentedInvariance
import OAI.Analysis.IrrationalRotation.Product.ProductFieldRepresentation
import OAI.Analysis.IrrationalRotation.Product.ProductPowerIdentity
import OAI.Analysis.IrrationalRotation.Rotation.WeightedOrbitInvariance
import OAI.Analysis.IrrationalRotation.Product.ProductCocycleInterchange
import OAI.Analysis.IrrationalRotation.Product.ProductPairRatios

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Invariant233.ProductModel

def actualWeightField (θ c : ℕ → ℝ) (x : Base) : WeightedShift.Weight :=
  multiplierField θ (fun y => (weight θ c y : ℂ)) 1 (fun y => by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (weight_mem_Icc θ c y).1] using (weight_mem_Icc θ c y).2) x

@[simp] theorem actualWeightField_apply (θ c : ℕ → ℝ) (x : Base) (k : ℤ) :
    actualWeightField θ c x k = (weight θ c (rotationIterate θ k x) : ℂ) := rfl

theorem weightedOperator_ae_actualWeightField (θ c : ℕ → ℝ) (f : Hilbert) :
    weightedOperator θ c f =ᵐ[baseMeasure] fun x =>
      WeightedShift.operator (actualWeightField θ c x) (f x) := by
  have ha (x : Base) : ‖actualWeightField θ c x‖ ≤ 1 :=
    lp.norm_le_of_forall_le (by norm_num) (fun k => by
      simpa only [actualWeightField_apply, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (weight_mem_Icc θ c _).1] using (weight_mem_Icc θ c _).2)
  have hm (k : ℤ) : AEStronglyMeasurable
      (fun x => actualWeightField θ c x k) baseMeasure :=
    ((measurable_weight θ c).complex_ofReal.comp
      (rotationIterate_measurePreserving θ k).measurable).aestronglyMeasurable
  exact WeightedShift.fieldOperator_ae (actualWeightField θ c) 1 (by norm_num) ha hm f

theorem ae_actualWeightField_invariant (θ c : ℕ → ℝ)
    (p : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F x) * WeightedShift.operator (actualWeightField θ c x) * F x = 0 :=
  L2Multiplication.ae_invariance_of_represented
    (default : HilbertBasis ℤ ℂ Fiber) p (weightedOperator θ c) F
    (fun x => WeightedShift.operator (actualWeightField θ c x))
    hrep (weightedOperator_ae_actualWeightField θ c) hinv

theorem boundedDiagonal_weight (w : WeightedShift.Weight) :
    SequenceHilbert.boundedDiagonal (fun k : ℤ => w k) = WeightedShift.diagonal w := by
  ext v k
  rw [SequenceHilbert.boundedDiagonal_apply_of_bound _ ‖w‖ (norm_nonneg w)
    (fun i => lp.norm_apply_le_norm (by simp) w i)]
  rfl

theorem ratioDiagonal_eq_normalized_orbit (θ c : ℕ → ℝ)
    (x : Base) (n : ℕ)
    (hprod : ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x))
    (hratio : ∀ k : ℤ,
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x) :
    ratioDiagonal θ c x (rotationIterate θ n x) =
      WeightedShift.diagonal ((ProductCocycle.cocycleVersion θ c n x : ℂ)⁻¹ •
        WeightedShift.orbitProduct (actualWeightField θ c x) n) := by
  rw [← boundedDiagonal_weight]
  apply SequenceHilbert.boundedDiagonal_congr
  intro k
  change (cocycleRatio θ c x (rotationIterate θ n x) k : ℂ) =
    (ProductCocycle.cocycleVersion θ c n x : ℂ)⁻¹ *
      (∏ j ∈ Finset.range n, (weight θ c (rotationIterate θ (k + j) x) : ℂ))
  rw [hratio k, Complex.ofReal_div, ← Complex.ofReal_prod, hprod k]
  exact div_eq_mul_inv _ _ |>.trans (mul_comm _ _)

theorem ae_orbit_pair_identity_of_ratio (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ)
    (F : Base → Fiber →L[ℂ] Fiber) (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0)
    (n : ℕ)
    (hratio : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      cocycleRatio θ c x (rotationIterate θ n x) k =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k x) /
          ProductCocycle.cocycleVersion θ c n x) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F (rotationIterate θ n x)) *
        ratioDiagonal θ c x (rotationIterate θ n x) * F x = 0 := by
  filter_upwards [ae_actualWeightField_invariant θ c p F hrep hinv,
    field_conjugacy hpM F hrep,
    ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n,
    hratio] with x hInv hCov hProd hRatio
  rw [ratioDiagonal_eq_normalized_orbit θ c x n hProd hRatio, hCov n]
  exact OrbitInvariance.weighted_shift_orbit_normalized
    (actualWeightField θ c x) (hproj x).isIdempotentElem hInv n
    (ProductCocycle.cocycleVersion θ c n x : ℂ)

theorem ae_orbit_pair_identity (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (hpM : p ∈ factor θ)
    (F : Base → Fiber →L[ℂ] Fiber) (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure,
      (1 - F (rotationIterate θ n x)) *
        ratioDiagonal θ c x (rotationIterate θ n x) * F x = 0 :=
  ae_orbit_pair_identity_of_ratio θ c hθ0 hc hθ p hpM F hproj hrep hinv n
    ((ae_cocycleRatio_rotation θ hθ0 hθ).mono (fun _ hx k => hx c k n))

end Invariant233.ProductModel

end

end OAI
