import OAI.Analysis.IrrationalRotation.Operators.BlockedProjectionWindow
import OAI.Analysis.IrrationalRotation.Product.ProductOrbitPair

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ComplexConjugate ENNReal

namespace Invariant233.ProductModel

theorem pairIdentity_diagonal_weight (θ c : ℕ → ℝ) (x y : Base)
    (hr : ∀ k, 0 < cocycleRatio θ c x y k ∧ cocycleRatio θ c x y k ≤ 1) :
    ∃ r : WeightedShift.Weight,
      (∀ k, r k = (cocycleRatio θ c x y k : ℂ)) ∧
      WeightedShift.diagonal r = ratioDiagonal θ c x y := by
  let r : WeightedShift.Weight := ⟨fun k => (cocycleRatio θ c x y k : ℂ),
    memℓp_infty (by
      refine ⟨1, ?_⟩
      rintro t ⟨k, rfl⟩
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr k).1]
        using (hr k).2)⟩
  exact ⟨r, fun _ => rfl, (boundedDiagonal_weight r).symm⟩

theorem cocycle_convolution_of_pairIdentity
    (θ c : ℕ → ℝ) (F : Base → Fiber →L[ℂ] Fiber) (x y : Base)
    (hproj : IsStarProjection (F y))
    (hinv : (1 - F y) * WeightedShift.operator (actualWeightField θ c y) * F y = 0)
    (hpair : PairIdentity θ c F (x, y)) (n : ℕ)
    (hprod : ∀ v : ℤ, (∏ i ∈ Finset.range n,
      weight θ c (rotationIterate θ (v + i) y)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ v y))
    (hadd : ∀ v : ℤ, ProductCocycle.cocycleVersion θ c (v + n) y =
      ProductCocycle.cocycleVersion θ c n (rotationIterate θ v y) *
        ProductCocycle.cocycleVersion θ c v y)
    (ξ η : Fiber) :
    let A : ℤ → ℂ := fun v => F x ξ v / (ProductCocycle.cocycleVersion θ c v x : ℂ)
    let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) y : ℂ) *
      conj ((1 - F y) η (-v))
    Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  obtain ⟨r, hr, hdiag⟩ := pairIdentity_diagonal_weight θ c x y hpair.1
  apply OrbitInvariance.cocycle_coefficients_absolute_and_zero
    (actualWeightField θ c y) r
    (fun v => ProductCocycle.cocycleVersion θ c v x)
    (fun v => ProductCocycle.cocycleVersion θ c v y) hproj hinv
    (by rw [hdiag]; exact hpair.2) n ξ η
  intro v
  rw [WeightedShift.orbitProduct_apply, hr]
  change (∏ i ∈ Finset.range n, (weight θ c (rotationIterate θ (v + i) y) : ℂ)) *
    (ProductCocycle.cocycleVersion θ c v y /
      ProductCocycle.cocycleVersion θ c v x : ℝ) = _
  rw [← Complex.ofReal_prod, hprod v, hadd v, Complex.ofReal_div, Complex.ofReal_mul]
  ring

end Invariant233.ProductModel

namespace Invariant233.BlockedProductCoupling

theorem ae_source_convolution_absolute_and_zero {p : ProductScaleData}
    (hp : ProductScaleLaws p) (e : ℕ ≃ Σ s, Fin (p.m s))
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (P : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert) (F : ProjectionField)
    (hrep : ∀ ξ : ProductModel.Hilbert,
      P ξ =ᵐ[ProductModel.baseMeasure] fun x => F x (ξ x))
    (hinv : (1 - P) * ProductModel.weightedOperator θ (fun i => p.C (e i).1) * P = 0)
    (hproj : ∀ᵐ x ∂ProductModel.baseMeasure, IsStarProjection (F x))
    (j : ℕ)
    (hpair : ∀ᵐ z ∂sourceLaw p j, ProductModel.PairIdentity θ (fun i => p.C (e i).1)
      F (circleLeftEndpoint e z, circleRightEndpoint e z)) :
    ∀ᵐ z ∂sourceLaw p j, ∀ n : ℕ,
      Summable (fun v : ℤ => ‖sourceCoefficientA p e θ F z v *
        sourceCoefficientB p e θ F z (-(n : ℤ) - v)‖) ∧
      (∑' v : ℤ, sourceCoefficientA p e θ F z v *
        sourceCoefficientB p e θ F z (-(n : ℤ) - v)) = 0 := by
  let c : ℕ → ℝ := fun i => p.C (e i).1
  have hc : ∀ i, 0 ≤ c i := fun i => (hp.C_pos (e i).1).le
  have hright := sourceLaw_quasiMeasurePreserving_right hp e j
  have hInv := ProductModel.ae_actualWeightField_invariant θ c P F hrep hinv
  obtain ⟨s, _, hfull, _, _, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθsum
  have hProd : ∀ᵐ y ∂ProductModel.baseMeasure, ∀ n : ℕ, ∀ v : ℤ,
      (∏ i ∈ Finset.range n, ProductModel.weight θ c (ProductModel.rotationIterate θ (v + i) y)) =
        ProductCocycle.cocycleVersion θ c n (ProductModel.rotationIterate θ v y) :=
    ae_all_iff.mpr (fun n => ProductModel.ae_weight_orbit_product_eq_cocycleVersion
      θ c hθ0 hc hθsum n)
  filter_upwards [hpair, hright.ae hproj, hright.ae hInv,
    hright.ae hProd, hright.ae hfull] with z hz hpz hiz hprod hcore
  intro n
  exact ProductModel.cocycle_convolution_of_pairIdentity θ c F
    (circleLeftEndpoint e z) (circleRightEndpoint e z) hpz hiz hz n (hprod n)
    (fun v => hlaw _ hcore c v n) sourceBasisZero sourceBasisZero

end Invariant233.BlockedProductCoupling

end

end OAI
