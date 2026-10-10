import OAI.Geometry.RCD.Coordinates.CenteredSplitting
import OAI.Geometry.RCD.Sobolev.CenteredAffineSobolev

namespace OAI

/-! # Compatibility of centered point values with the normalizing frame -/

open Set MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Continuous representatives of the same Sobolev columns have the exact
covector transformation law, including at the center of an open ball. -/
theorem framed_covector_point_values [μ.IsOpenPosMeasure] {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (s : Set X) (hs : IsOpen s) (V W : X → Euclidean n)
    (hV : ContinuousOn V s) (hW : ContinuousOn W s)
    (hu : ∀ j, SobolevSpace.toLp μ hQ (u j) =ᵐ[μ.restrict s] fun x => V x j)
    (hNu : ∀ j, SobolevSpace.toLp μ hQ (transformedColumn μ hQ u N j) =ᵐ[
      μ.restrict s] fun x => W x j) (b : Euclidean n) :
    EqOn (fun x => ⟪W x, N.symm b⟫_ℝ) (fun x => ⟪V x, b⟫_ℝ) s := by
  have hw := sobolevColumnMap_representative μ hQ (transformedColumn μ hQ u N)
    s W hNu (N.symm b)
  simp only [sobolevColumnMap_transformed, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at hw
  have hv := sobolevColumnMap_representative μ hQ u s V hu b
  exact Measure.eqOn_open_of_ae_eq (hw.symm.trans hv) hs
    (hW.inner continuousOn_const) (hV.inner continuousOn_const)

/-- Centering before applying the inverse covector frame gives the same
actual Sobolev function as centering the original coordinate covector. -/
theorem centered_frame_covector_eq {n : ℕ}
    (u : Fin n → SobolevSpace μ hQ) (N : Euclidean n ≃L[ℝ] Euclidean n)
    (η : SobolevSpace μ hQ) (c cN b : Euclidean n)
    (hc : ⟪cN, N.symm b⟫_ℝ = ⟪c, b⟫_ℝ) :
    sobolevColumnMap μ hQ (centeredColumn μ hQ (transformedColumn μ hQ u N) cN η)
      (N.symm b) = centeredAffineSobolev μ hQ u η c b := by
  rw [centeredColumn, sobolevColumnMap_affineChanged]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    neg_apply, innerSL_apply_apply, sobolevColumnMap_transformed,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, hc,
    centeredAffineSobolev]
  exact add_comm _ _

end RegularPointCoordinates

end

end OAI
