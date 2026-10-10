import OAI.Analysis.IrrationalRotation.Product.ProductConvolutionIdentity
import OAI.Analysis.IrrationalRotation.Product.SourceProductTailRealization
import OAI.Analysis.IrrationalRotation.Product.ProductObstructionConstant

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

abbrev sourceUnitVector : Fiber := lp.single 2 (0 : ℤ) (1 : ℂ)

def sourceLeftVector (F : Base → Fiber →L[ℂ] Fiber) (ω : Sample) : Fiber :=
  F (circleLeftEndpoint ω) sourceUnitVector

def sourceRightVector (F : Base → Fiber →L[ℂ] Fiber) (ω : Sample) : Fiber :=
  (1 - F (circleRightEndpoint ω)) sourceUnitVector

def sourceLeftCocycle (θ c : ℕ → ℝ) (ω : Sample) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k (circleLeftEndpoint ω)

def sourceRightCocycle (θ c : ℕ → ℝ) (ω : Sample) (k : ℤ) : ℝ :=
  ProductCocycle.cocycleVersion θ c k (circleRightEndpoint ω)

theorem conditionalData_of_sourceTail
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (P : Parameters) (j : ℕ)
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hfst : (circlePairLaw P).map Prod.fst ≪ baseMeasure)
    (hsnd : (circlePairLaw P).map Prod.snd ≪ baseMeasure)
    (hpair : ∀ᵐ xy ∂circlePairLaw P, PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : SourceTailEstimate p e θ j P)
    (E : Set Sample) (hE : MeasurableSet E) (c : ℝ) (hmass : c ≤ (law P).real E)
    (hcoeff : ∀ᵐ ω ∂(law P).restrict E,
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖coeffA (sourceLeftVector F) (sourceLeftCocycle θ (fun i => p.C (e i).1)) ω v‖ ≤ p.coefficientBound j) ∧
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
        ‖coeffB (sourceRightVector F) (sourceRightCocycle θ (fun i => p.C (e i).1)) ω v‖ ≤ p.coefficientBound j) ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤
        ‖coeffA (sourceLeftVector F) (sourceLeftCocycle θ (fun i => p.C (e i).1)) ω 0‖ ∧
      1 / ((j + 1 : ℕ) : ℝ) ≤
        ‖coeffB (sourceRightVector F) (sourceRightCocycle θ (fun i => p.C (e i).1)) ω 0‖)
    (htag : ∀ᵐ ω ∂(law P).restrict E,
      ∃ i ∈ ProductPhases.consecutiveBlock p.m j,
        circleRepresentative (circleLeftEndpoint ω i) < 1 / (p.m j : ℝ) ∧
        1 - 1 / (p.m j : ℝ) ≤ circleRepresentative (circleRightEndpoint ω i)) :
    Nonempty (Data Sample (law P) (p.K j) (p.coefficientBound j)
      (1 / ((j + 1 : ℕ) : ℝ)) c (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  let costs : ℕ → ℝ := fun i => p.C (e i).1
  have hc : ∀ i, 0 ≤ costs i := fun i => (hp.C_pos (e i).1).le
  have hxy : Measurable (fun ω : Sample => (circleLeftEndpoint ω, circleRightEndpoint ω)) :=
    circleLeftEndpoint_measurable.prodMk circleRightEndpoint_measurable
  have hz := ae_of_ae_map hxy.aemeasurable
    (ae_coefficients_absolute_and_zero θ costs hθ0 hc hθsum A F hproj hF.2.2.2.1
      hinv (circlePairLaw P) hsnd hpair sourceUnitVector sourceUnitVector)
  have hr := ae_of_ae_map hxy.aemeasurable
    (ae_convolution_two_ratio_bounds θ costs hθ0 hc hθsum F (circlePairLaw P) hfst hsnd hpair)
  obtain ⟨H₁, H₂, hm₁, hm₂, ht⟩ := htail
  have hv : ‖sourceUnitVector‖ = 1 := by simp [sourceUnitVector]
  refine ⟨{
    mX := MeasurableSpace.comap circleLeftEndpoint inferInstance
    mY := MeasurableSpace.comap circleRightEndpoint inferInstance
    mX_le := circleLeftEndpoint_measurable.comap_le
    mY_le := circleRightEndpoint_measurable.comap_le
    ξ := sourceLeftVector F
    γ := sourceRightVector F
    ξ_measurable := ?_
    γ_measurable := ?_
    ξ_unit := ?_
    γ_unit := ?_
    Fx := sourceLeftCocycle θ costs
    Fy := sourceRightCocycle θ costs
    Fx_measurable := fun k => (ProductCocycle.measurable_cocycleVersion θ costs k).comp circleLeftEndpoint_measurable
    Fy_measurable := fun k => (ProductCocycle.measurable_cocycleVersion θ costs k).comp circleRightEndpoint_measurable
    Fx_pos := Filter.Eventually.of_forall (fun ω k => ProductCocycle.cocycleVersion_pos θ costs k _)
    Fy_pos := Filter.Eventually.of_forall (fun ω k => ProductCocycle.cocycleVersion_pos θ costs k _)
    Fx_zero := Filter.Eventually.of_forall (fun ω => ProductCocycle.cocycleVersion_zero θ costs _)
    Fy_zero := Filter.Eventually.of_forall (fun ω => ProductCocycle.cocycleVersion_zero θ costs _)
    zero_convolution := ?_
    ratio_bounds := ?_
    E := E
    E_measurable := hE
    E_mass := hmass
    coefficient_bounds := hcoeff
    H₁ := H₁
    H₂ := H₂
    H₁_measurable := hm₁
    H₂_measurable := hm₂
    attenuation := ?_
    conditional₁ := ?_
    conditional₂ := ?_ }⟩
  · exact (hF.2.2.1 sourceUnitVector).comp_measurable (Measurable.of_comap_le le_rfl)
  · have hs : StronglyMeasurable (fun x : Base => (1 - F x) sourceUnitVector) := by
      convert ((stronglyMeasurable_const : StronglyMeasurable (fun _ : Base => sourceUnitVector)).sub (hF.2.2.1 sourceUnitVector)) using 1
      funext x
      simp only [sub_apply, one_apply_eq_self, Pi.sub_apply]
    exact hs.comp_measurable (Measurable.of_comap_le le_rfl)
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := (F (circleLeftEndpoint ω)).le_of_opNorm_le
        (IsStarProjection.norm_le _ (hproj _)) sourceUnitVector
      simpa [sourceLeftVector, hv] using h)
  · exact Filter.Eventually.of_forall (fun ω => by
      have h := (1 - F (circleRightEndpoint ω)).le_of_opNorm_le
        (IsStarProjection.norm_le _ (hproj _).one_sub) sourceUnitVector
      simpa [sourceRightVector, hv] using h)
  · intro n _
    filter_upwards [hz] with ω hω
    exact (hω n).2
  · intro n _
    filter_upwards [hr] with ω hω v
    exact hω n v
  · filter_upwards [ae_restrict_of_ae ht, htag] with ω hω htagω k hk
    have hk' : (p.K j : ℝ) < |(k : ℝ)| := by exact_mod_cast hk
    exact (hω k hk').2.2 htagω
  · intro k hk
    filter_upwards [ht] with ω hω
    exact (hω k (by exact_mod_cast hk)).1
  · intro k hk
    filter_upwards [ht] with ω hω
    exact (hω k (by exact_mod_cast hk)).2.1

end Invariant233.ProductModel

end

end OAI
