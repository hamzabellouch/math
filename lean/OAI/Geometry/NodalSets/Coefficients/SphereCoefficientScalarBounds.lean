import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Coefficients.SphereCoefficientFormComparison

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

def coefficientPrincipalEntry (i j : Fin 4) : CoefficientPoint BaseModel →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp ((ContinuousLinearMap.apply ℝ BaseModel (EuclideanSpace.proj j)).comp
    (ContinuousLinearMap.fst ℝ ((BaseModel →L[ℝ] ℝ) →L[ℝ] BaseModel) ℝ))

theorem coefficientPrincipalEntry_apply (A : IntrinsicTensor) (rho : Base → ℝ)
    (p : Base) (z : BaseModel) (i j : Fin 4) :
    coefficientPrincipalEntry i j (intrinsicChartCoefficient A rho p z) =
      intrinsicSphereChartTensor A p z i j := by
  change (matrixContravariant (intrinsicSphereChartTensor A p z) (EuclideanSpace.proj j)) i = _
  have h := congrFun (matrixContravariant_coordinates (intrinsicSphereChartTensor A p z)
    (EuclideanSpace.proj j)) i
  simpa [Matrix.mulVec,dotProduct,baseCovectorCoordinates,EuclideanSpace.basisFun_apply,
    Pi.single_apply] using h

theorem sphereCoefficientDistance_scalar_derivative_bound (P : Finset Base) (J : ℕ)
    (d b : SphereEnergyData)
    (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density)
    (L : CoefficientPoint BaseModel →L[ℝ] ℝ)
    (p : Base) (hp : p ∈ P) (x : Yau.Jets.Coord) (hx : x ∈ Metric.closedBall 0 1)
    (k : ℕ) (hk : k ≤ J) :
    ‖iteratedFDeriv ℝ k (fun y ↦ L (intrinsicChartCoefficient b.tensor b.density p (seedCoordEquiv y)-
      intrinsicChartCoefficient d.tensor d.density p (seedCoordEquiv y))) x‖ ≤
      (‖L‖ * (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J) *
        sphereCoefficientDistance P J d.tensor d.density b.tensor b.density := by
  let F : BaseModel → CoefficientPoint BaseModel := fun z ↦
    intrinsicChartCoefficient b.tensor b.density p z-intrinsicChartCoefficient d.tensor d.density p z
  have hF : ContDiff ℝ ∞ F :=
    (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb p).sub
      (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd p)
  have hsize : ‖iteratedFDeriv ℝ k F (seedCoordEquiv x)‖ ≤
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density :=
    norm_le_finiteChartDerivativeSize P sphereAtlasCore_compact J _
      (fun q _ ↦ (intrinsic_coefficient_chart_smooth b.tensor b.smooth b.symm b.pos b.density hb q).sub
        (intrinsic_coefficient_chart_smooth d.tensor d.smooth d.symm d.pos d.density hd q))
      p hp k hk _ ⟨x,hx,rfl⟩
  have hkfin : (k : ℕ∞ω) ≤ ∞ := by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top)
  change ‖iteratedFDeriv ℝ k (L ∘ (F ∘ seedCoordEquiv.toContinuousLinearMap)) x‖ ≤ _
  rw [L.iteratedFDeriv_comp_left (hF.comp seedCoordEquiv.toContinuousLinearMap.contDiff).contDiffAt hkfin]
  apply (L.norm_compContinuousMultilinearMap_le _).trans
  rw [seedCoordEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hF x hkfin]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k F (seedCoordEquiv x)) (fun _ ↦ seedCoordEquiv.toContinuousLinearMap)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hcomp
  have hpow : ‖seedCoordEquiv.toContinuousLinearMap‖^k ≤ (max 1 ‖seedCoordEquiv.toContinuousLinearMap‖)^J :=
    (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) k).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have hnonneg : 0 ≤ sphereCoefficientDistance P J d.tensor d.density b.tensor b.density :=
    (norm_nonneg _).trans hsize
  have hbound := hcomp.trans (mul_le_mul hsize hpow (by positivity) hnonneg)
  exact (mul_le_mul_of_nonneg_left hbound (norm_nonneg L)).trans_eq (by ring)

end
end Yau.Target

end OAI
