import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialSmooth
import OAI.Geometry.SurfaceImmersion.Correction.AtlasPolynomialLinearity

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance polynomialIncrementFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialIncrementFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialIncrementDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialIncrementDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialIncrementSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialIncrementSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)





/-- Combine the actual free, forced and mean residuals, with the derived
mixed-polynomial and Taylor bounds, into a bound for the changed metric. -/
theorem atlas_polynomial_increment_bound (m : ℕ) (A₀ B₀ : ℝ)
    (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : A.centers → ℕ}
      (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
      (_hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
      (F U V : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ContMDiff planeModel spaceModel ∞ U → ContMDiff planeModel spaceModel ∞ V →
      ∀ (T H : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (T p)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      ∀ (τ ε δ C₁ C₂ C₃ E₁ E₂ : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ →
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁
        (linearMetricTensor F U+A.atlasPolynomialVariation P ε F U) →
      A.TensorWeightedBound τ m C₂
        (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
          (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H) →
      A.TensorWeightedBound τ m C₃ (H-T) →
      A.TensorWeightedBound τ m (E₁*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U) →
      A.TensorWeightedBound τ m (E₂*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F (U+V)) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+(D+E₁+E₂)*(δ^3/τ))
        (A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T) := by
  obtain ⟨D,hD,hd⟩ := A.global_cubic_remainder_bound m A₀ B₀ hA hB
  refine ⟨D,hD,?_⟩
  intro n P hP F U V hF hU hV T H hT hH τ ε δ C₁ C₂ C₃ E₁ E₂
    hτ hτ1 hδ hδτ hbU hbV h₁ h₂ h₃ h₄ h₅
  have hUV := hU.add hV
  have hLU := (A.linearMetricTensor_smooth hF hU).add_section
    (A.atlasPolynomialVariation_smooth hP hF hU ε)
  have hLV := (A.linearMetricTensor_smooth hF hV).add_section
    (A.atlasPolynomialVariation_smooth hP hF hV ε)
  have hQU := (A.inducedTensor_smooth hU).add_section
    (A.atlasPolynomialQuadratic_smooth hP hF hU ε)
  have hs₂ := (hLV.add_section hQU).sub_section hH
  have hs₃ := hH.sub_section hT
  have hM := (A.linearMetricTensor_smooth hU hV).add_section (A.inducedTensor_smooth hV)
  have hPol := (A.atlasPolynomialQuadratic_smooth hP hF hUV ε).sub_section
    (A.atlasPolynomialQuadratic_smooth hP hF hU ε)
  have hRem := A.atlasPolynomialRemainder_smooth hP hF hUV ε
  have hb₁ := A.tensorWeightedBound_add hLU hs₂ hτ.le h₁ h₂
  have hb₂ := A.tensorWeightedBound_add (hLU.add_section hs₂) hs₃ hτ.le hb₁ h₃
  have hb₃ := A.tensorWeightedBound_add ((hLU.add_section hs₂).add_section hs₃) hM hτ.le hb₂
    (hd τ δ hτ hτ1 hδ hδτ U V hU hV hbU hbV)
  have hb₄ := A.tensorWeightedBound_add
    (((hLU.add_section hs₂).add_section hs₃).add_section hM) hPol hτ.le hb₃ h₄
  have hb₅ := A.tensorWeightedBound_add
    ((((hLU.add_section hs₂).add_section hs₃).add_section hM).add_section hPol) hRem hτ.le hb₄ h₅
  have hlin : linearMetricTensor F (U+V) = linearMetricTensor F U+linearMetricTensor F V := by
    have hh := linearMetricTensor_finite_sum F ![U,V] (by
      intro j
      fin_cases j
      · exact hU
      · exact hV)
    convert hh using 1
    · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    · funext p
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.add_apply]
  have herr : A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T =
      (((((linearMetricTensor F U+A.atlasPolynomialVariation P ε F U)+
        (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
          (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H))+(H-T))+
        (linearMetricTensor U V+inducedTensor V))+
        (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U))+
        A.atlasPolynomialRemainder P ε F (U+V) := by
    rw [A.atlas_polynomial_metric_taylor_identity P ε hF hUV,
      A.atlasPolynomialVariation_add P ε F hU hV,hlin,inducedTensor_add hU hV]
    abel
  rw [herr]
  convert hb₅ using 1
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
