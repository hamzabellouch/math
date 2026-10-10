import OAI.Geometry.NodalSets.Elliptic.IntrinsicRealCoordinates

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsic_differential_pair_chart (A : IntrinsicTensor) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (p : Base) (x : Yau.Jets.Coord) :
    A (sphereChartCoordMap p x) (sphereDifferential u (sphereChartCoordMap p x))
      (sphereDifferential v (sphereChartCoordMap p x)) =
      ∑ i, ∑ j, Yau.coordPartial (u ∘ sphereChartCoordMap p) x i*
        intrinsicRealPrincipal A p x i j*Yau.coordPartial (v ∘ sphereChartCoordMap p) x j := by
  rw [sphereDifferential_chart u hu,sphereDifferential_chart v hv]
  change A ((extChartAt (𝓡 4) p).symm (seedCoordEquiv x)) _ _ = _
  rw [← intrinsicAmbientMatrix_chart_pairing,← intrinsicSphereChartTensor_eq]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,intrinsicRealPrincipal,mul_assoc]

lemma intrinsic_differential_pair_pullback_smooth (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    ContDiff ℝ ∞ (fun x ↦ A (sphereChartCoordMap p x)
      (sphereDifferential u (sphereChartCoordMap p x)) (sphereDifferential v (sphereChartCoordMap p x))) := by
  simp_rw [intrinsic_differential_pair_chart A u v hu hv]
  exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
    (((Yau.real_coordPartial_smooth _ (spherePullback_smooth u hu p) i).mul
      (intrinsicRealPrincipal_smooth A hA hs hp p i j)).mul
        (Yau.real_coordPartial_smooth _ (spherePullback_smooth v hv p) j))))

end
end Yau.Target

end OAI
