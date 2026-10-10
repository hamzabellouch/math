import OAI.Geometry.NodalSets.Elliptic.IntrinsicRealCoordinates
import OAI.Geometry.NodalSets.Elliptic.RealEllipticLinearity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsicWeightedChartOperator_linear_combination (A : IntrinsicTensor)
    (hA : IntrinsicTensorSmooth A) (hs : ∀ p v w, A p v w = A p w v)
    (hp : ∀ p v, v ≠ 0 → 0 < A p v v) (rho : Base → ℝ)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (c : ℝ) (p : Base) (z : BaseModel) :
    intrinsicWeightedChartOperator A rho (fun q ↦ c*u q+v q) p z =
      c*intrinsicWeightedChartOperator A rho u p z+intrinsicWeightedChartOperator A rho v p z := by
  obtain ⟨x,rfl⟩ := seedCoordEquiv.surjective z
  rw [intrinsicRealOperator_pullback,intrinsicRealOperator_pullback,intrinsicRealOperator_pullback]
  change (rho (sphereChartCoordMap p x))⁻¹ *
    realWeightedElliptic roundCoordDensity (intrinsicRealPrincipal A p)
      (fun y ↦ c*(u ∘ sphereChartCoordMap p) y+(v ∘ sphereChartCoordMap p) y) x =
    c*((rho (sphereChartCoordMap p x))⁻¹ * realWeightedElliptic roundCoordDensity
      (intrinsicRealPrincipal A p) (u ∘ sphereChartCoordMap p) x)+
    (rho (sphereChartCoordMap p x))⁻¹ * realWeightedElliptic roundCoordDensity
      (intrinsicRealPrincipal A p) (v ∘ sphereChartCoordMap p) x
  rw [realWeightedElliptic_linear_combination _ _ _ _ roundCoordDensity_smooth
    (intrinsicRealPrincipal_smooth A hA hs hp p) (spherePullback_smooth u hu p) (spherePullback_smooth v hv p)]
  ring

theorem intrinsic_eigenfunction_linear_combination (A : IntrinsicTensor)
    (hA : IntrinsicTensorSmooth A) (hs : ∀ p v w, A p v w = A p w v)
    (hp : ∀ p v, v ≠ 0 → 0 < A p v v) (rho : Base → ℝ)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (lam : ℝ)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (c : ℝ) : ∀ p z, -intrinsicWeightedChartOperator A rho (fun q ↦ c*u q+v q) p z =
      lam*(c*u ((extChartAt (𝓡 4) p).symm z)+v ((extChartAt (𝓡 4) p).symm z)) := by
  intro p z
  rw [intrinsicWeightedChartOperator_linear_combination A hA hs hp rho u v hu hv]
  linear_combination c*heu p z+hev p z

end
end Yau.Target

end OAI
