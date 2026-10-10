import OAI.Analysis.IrrationalRotation.Couplings.ProductPairIdentity
import OAI.Analysis.IrrationalRotation.Rotation.CocycleWindowBounds
import OAI.Analysis.IrrationalRotation.Analysis.ConvolutionRatios

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators ComplexConjugate

namespace Invariant233.ProductModel

theorem ae_antitone_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, Antitone (fun k : ℤ => ProductCocycle.cocycleVersion θ c k x) := by
  obtain ⟨s, _hsm, hfull, _hinv, _hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx
  intro a b hab
  have heq := hlaw x hx c a (b - a)
  rw [add_sub_cancel] at heq
  calc
    ProductCocycle.cocycleVersion θ c b x =
        ProductCocycle.cocycleVersion θ c (b - a) (rotationIterate θ a x) *
          ProductCocycle.cocycleVersion θ c a x := heq
    _ ≤ 1 * ProductCocycle.cocycleVersion θ c a x :=
      mul_le_mul_of_nonneg_right
        (ProductCocycle.cocycleVersion_le_one_of_nonneg_time θ c hθ0 hc (b - a)
          (sub_nonneg.mpr hab) _) (ProductCocycle.cocycleVersion_pos θ c a x).le
    _ = _ := one_mul _

theorem ae_convolution_two_ratio_bounds (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (F : Base → Fiber →L[ℂ] Fiber) (ν : Measure EndpointPair)
    (hfst : ν.map Prod.fst ≪ baseMeasure) (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂ν, PairIdentity θ c F xy) :
    ∀ᵐ xy ∂ν, ∀ (n : ℕ) (v : ℤ),
      0 < ProductCocycle.cocycleVersion θ c ((n : ℤ) + v) xy.2 /
        ProductCocycle.cocycleVersion θ c v xy.1 ∧
      ProductCocycle.cocycleVersion θ c ((n : ℤ) + v) xy.2 /
          ProductCocycle.cocycleVersion θ c v xy.1 ≤
        min (cocycleRatio θ c xy.1 xy.2 v)
          (cocycleRatio θ c xy.1 xy.2 ((n : ℤ) + v)) ∧
      min (cocycleRatio θ c xy.1 xy.2 v)
        (cocycleRatio θ c xy.1 xy.2 ((n : ℤ) + v)) ≤ 1 := by
  have hmono := ae_antitone_cocycleVersion θ c hθ0 hc hθ
  have hx := ae_of_ae_map measurable_fst.aemeasurable (hfst.ae_le hmono)
  have hy := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hmono)
  filter_upwards [hx, hy, hpair] with xy hx hy hp n v
  exact InvariantProjection.cocycle_two_ratio_bounds
    (fun k => ProductCocycle.cocycleVersion θ c k xy.1)
    (fun k => ProductCocycle.cocycleVersion θ c k xy.2)
    (fun k => ProductCocycle.cocycleVersion_pos θ c k xy.1)
    (fun k => ProductCocycle.cocycleVersion_pos θ c k xy.2)
    hx hy (fun k => (hp.1 k).2) n v

theorem coefficients_absolute_and_zero_of_pair (θ c : ℕ → ℝ)
    (F : Base → Fiber →L[ℂ] Fiber) (x y : Base)
    (hproj : IsStarProjection (F y))
    (hinv : (1 - F y) * WeightedShift.operator (actualWeightField θ c y) * F y = 0)
    (hpair : PairIdentity θ c F (x, y)) (n : ℕ)
    (hprod : ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) y)) =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k y))
    (hlaw : ∀ k : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) y =
        ProductCocycle.cocycleVersion θ c n (rotationIterate θ k y) *
          ProductCocycle.cocycleVersion θ c k y)
    (ξ η : Fiber) :
    let A : ℤ → ℂ := fun v => F x ξ v / (ProductCocycle.cocycleVersion θ c v x : ℂ)
    let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) y : ℂ) *
      star (((1 - F y) η) (-v))
    (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  let r : WeightedShift.Weight := ⟨fun k => (cocycleRatio θ c x y k : ℂ),
    memℓp_infty ⟨1, by
      rintro z ⟨k, rfl⟩
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpair.1 k).1]
        using (hpair.1 k).2⟩⟩
  have hr : WeightedShift.diagonal r = ratioDiagonal θ c x y :=
    (boundedDiagonal_weight r).symm
  have hp : (1 - F y) * WeightedShift.diagonal r * F x = 0 := by
    rw [hr]
    exact hpair.2
  apply OrbitInvariance.cocycle_coefficients_absolute_and_zero
    (actualWeightField θ c y) r
    (fun k => ProductCocycle.cocycleVersion θ c k x)
    (fun k => ProductCocycle.cocycleVersion θ c k y)
    hproj hinv hp n ξ η
  intro v
  change (∏ j ∈ Finset.range n, (weight θ c (rotationIterate θ (v + j) y) : ℂ)) *
    ((ProductCocycle.cocycleVersion θ c v y /
      ProductCocycle.cocycleVersion θ c v x : ℝ) : ℂ) = _
  rw [← Complex.ofReal_prod, hprod v, Complex.ofReal_div, ← mul_div_assoc,
    ← Complex.ofReal_mul, ← hlaw v]

theorem ae_coefficients_absolute_and_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (p : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hproj : ∀ x, IsStarProjection (F x))
    (hrep : ∀ f : Hilbert, p f =ᵐ[baseMeasure] fun x => F x (f x))
    (hinv : (1 - p) * weightedOperator θ c * p = 0)
    (ν : Measure EndpointPair) (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂ν, PairIdentity θ c F xy) (ξ η : Fiber) :
    ∀ᵐ xy ∂ν, ∀ n : ℕ,
      let A : ℤ → ℂ := fun v => F xy.1 ξ v /
        (ProductCocycle.cocycleVersion θ c v xy.1 : ℂ)
      let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) xy.2 : ℂ) *
        star (((1 - F xy.2) η) (-v))
      (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
        (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hInv := ae_of_ae_map measurable_snd.aemeasurable
    (hsnd.ae_le (ae_actualWeightField_invariant θ c p F hrep hinv))
  obtain ⟨s, _hsm, hfull, _hinv, _hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  have hcore := ae_of_ae_map measurable_snd.aemeasurable (hsnd.ae_le hfull)
  apply ae_all_iff.mpr
  intro n
  have hProd := ae_of_ae_map measurable_snd.aemeasurable
    (hsnd.ae_le (ae_weight_orbit_product_eq_cocycleVersion θ c hθ0 hc hθ n))
  filter_upwards [hInv, hcore, hProd, hpair] with xy hi hs hp hxy
  exact coefficients_absolute_and_zero_of_pair θ c F xy.1 xy.2 (hproj xy.2)
    hi hxy n hp (fun k => hlaw xy.2 hs c k n) ξ η

theorem ae_coefficients_absolute_sum_le (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (F : Base → Fiber →L[ℂ] Fiber) (hproj : ∀ x, IsStarProjection (F x))
    (ν : Measure EndpointPair) (hfst : ν.map Prod.fst ≪ baseMeasure)
    (hsnd : ν.map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂ν, PairIdentity θ c F xy) (ξ η : Fiber) :
    ∀ᵐ xy ∂ν, ∀ n : ℕ,
      let A : ℤ → ℂ := fun v => F xy.1 ξ v /
        (ProductCocycle.cocycleVersion θ c v xy.1 : ℂ)
      let B : ℤ → ℂ := fun v => (ProductCocycle.cocycleVersion θ c (-v) xy.2 : ℂ) *
        star (((1 - F xy.2) η) (-v))
      (∑' v : ℤ, ‖A v * B (-(n : ℤ) - v)‖) ≤ ‖ξ‖ * ‖η‖ := by
  filter_upwards [ae_convolution_two_ratio_bounds θ c hθ0 hc hθ F ν hfst hsnd hpair]
    with xy hratio n
  dsimp only
  have hbound := InvariantProjection.l2_reindexed_multiplier_bound
    (F xy.1 ξ) ((1 - F xy.2) η) (Equiv.addLeft (n : ℤ))
    (fun v => ProductCocycle.cocycleVersion θ c ((n : ℤ) + v) xy.2 /
      ProductCocycle.cocycleVersion θ c v xy.1)
    (fun v => ⟨(hratio n v).1.le, (hratio n v).2.1.trans (hratio n v).2.2⟩)
  have hξ : ‖F xy.1 ξ‖ ≤ ‖ξ‖ := by
    simpa only [one_mul] using (F xy.1).le_of_opNorm_le
      (IsStarProjection.norm_le _ (hproj xy.1)) ξ
  have hη : ‖(1 - F xy.2) η‖ ≤ ‖η‖ := by
    simpa only [one_mul] using (1 - F xy.2).le_of_opNorm_le
      (IsStarProjection.norm_le _ (hproj xy.2).one_sub) η
  have hsum := hbound.2.trans (mul_le_mul hξ hη (norm_nonneg _) (norm_nonneg _))
  convert hsum using 1
  try rfl
  apply tsum_congr
  intro v
  congr 1
  rw [show -(-(n : ℤ) - v) = (n : ℤ) + v by omega]
  exact InvariantProjection.convolution_coefficient_factorization
    (fun k => ProductCocycle.cocycleVersion θ c k xy.1)
    (fun k => ProductCocycle.cocycleVersion θ c k xy.2)
    (F xy.1 ξ) ((1 - F xy.2) η) n v

end Invariant233.ProductModel

end

end OAI
