import OAI.Geometry.NodalSets.Charts.SphereWeightedNormalization
import OAI.Geometry.NodalSets.Spectral.IntrinsicEigenfunctionLinearity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry
open scoped ContDiff
noncomputable section

lemma intrinsic_eigenfunction_smul (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha) (rho : Base → ℝ)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (lam c : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z)) :
    ∀ p z, -intrinsicWeightedChartOperator A rho (c • u) p z =
      lam*(c • u) ((extChartAt (𝓡 4) p).symm z) := by
  have hc := intrinsic_eigenfunction_linear_combination A hA hs hp rho u u hu hu lam he he (c-1)
  have heq : (fun q ↦ (c-1)*u q+u q) = c • u := by
    funext q
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  intro p z
  rw [← heq]
  exact hc p z

theorem sphere_normalized_orthogonal_eigenfunction (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x alpha beta, A x alpha beta = A x beta alpha)
    (hp : ∀ x alpha, alpha ≠ 0 → 0 < A x alpha alpha)
    (rho : Base → ℝ) (hr : Continuous rho) (hrp : ∀ x, 0 < rho x)
    (u v : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0) (lam : ℝ)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z =
      lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z =
      lam*v ((extChartAt (𝓡 4) p).symm z))
    (hnot : ¬ ∃ c : ℝ, v = c • u) :
    ∃ w : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ w ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator A rho w p z =
        lam*w ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing rho w w = 1 ∧ sphereWeightedPairing rho w u = 0 := by
  obtain ⟨c,q,hq,hqs,hqo,hqzero⟩ := sphere_weighted_orthogonal_remainder rho u v hr hrp hu hv hune
  have hqne : q ≠ 0 := fun hz ↦ hnot ⟨c,hqzero.mp hz⟩
  have hqeq : q = fun x ↦ (-c)*u x+v x := by
    rw [hq]
    funext x
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hqe : ∀ p z, -intrinsicWeightedChartOperator A rho q p z =
      lam*q ((extChartAt (𝓡 4) p).symm z) := by
    rw [hqeq]
    exact intrinsic_eigenfunction_linear_combination A hA hs hp rho u v hu hv lam heu hev (-c)
  obtain ⟨s,w,_,hw,hws,hwne,hwn⟩ := sphere_weighted_normalization rho q hr hrp hqs hqne
  refine ⟨w,hws,hwne,?_,hwn,?_⟩
  · rw [hw]
    exact intrinsic_eigenfunction_smul A hA hs hp rho q hqs lam s hqe
  · rw [hw,sphereWeightedPairing_smul_left,hqo,mul_zero]

end
end Yau.Target

end OAI
