import OAI.Geometry.NodalSets.Elliptic.CoordinateMatrixEllipticity
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRealCoordinates

namespace OAI

namespace Yau.Target
open Manifold Matrix Yau.Geometry
open scoped ContDiff
noncomputable section

theorem intrinsic_real_uniform_ellipticity (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (p : Base) {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ c > 0, ∃ C > 0, ∀ x ∈ K, ∀ xi : Fin 4 → ℝ,
      c*(∑ i, xi i^2) ≤ (∑ i, ∑ j, xi i*intrinsicRealPrincipal A p x i j*xi j) ∧
      (∑ i, ∑ j, xi i*intrinsicRealPrincipal A p x i j*xi j) ≤ C*(∑ i, xi i^2) :=
  compact_matrix_uniform_ellipticity (intrinsicRealPrincipal A p)
    (fun i j ↦ (intrinsicRealPrincipal_smooth A hA hs hp p i j).continuous)
    (intrinsicRealPrincipal_posDef A hs hp p) hK

theorem intrinsic_real_lower_order_bound (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (lam : ℝ)
    (p : Base) {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, |intrinsicRealPotential rho lam p x| ≤ C ∧
      ∀ j, |intrinsicRealDrift A p x j| ≤ C := by
  let F : Yau.Jets.Coord → (Fin 4 → ℝ) × ℝ :=
    fun x ↦ (intrinsicRealDrift A p x,intrinsicRealPotential rho lam p x)
  have hF : Continuous F :=
    (continuous_pi (fun j ↦ (intrinsicRealDrift_smooth A hA hs hp p j).continuous)).prodMk
      (intrinsicRealPotential_smooth rho hr lam p).continuous
  obtain ⟨C,hC,hbound⟩ := (hK.image hF).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro x hx
  have hb := hbound _ ⟨x,hx,rfl⟩
  change max ‖intrinsicRealDrift A p x‖ |intrinsicRealPotential rho lam p x| ≤ C at hb
  refine ⟨(max_le_iff.mp hb).2,?_⟩
  intro j
  exact (norm_le_pi_norm (intrinsicRealDrift A p x) j).trans (max_le_iff.mp hb).1

theorem intrinsic_real_principal_differential_bound
    (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (w : Base → ℝ) (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) (lam : ℝ)
    (he : ∀ p z, -intrinsicWeightedChartOperator A rho w p z =
      lam*w ((extChartAt (𝓡 4) p).symm z))
    (p : Base) {K : Set Yau.Jets.Coord} (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K,
      |∑ i, ∑ j, intrinsicRealPrincipal A p x i j*
        Yau.coordPartial (fun y ↦ Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x i| ≤
      C*(|w (sphereChartCoordMap p x)| +
        ∑ j, |Yau.coordPartial (w ∘ sphereChartCoordMap p) x j|) := by
  obtain ⟨C,hC,hb⟩ := intrinsic_real_lower_order_bound A hA hs hp rho hr lam p hK
  refine ⟨C,hC,?_⟩
  intro x hx
  have heq := intrinsic_real_local_equation A hA hs hp rho hrp w hw lam he p x
  simp only [Function.comp_apply] at heq
  have hid : (∑ i, ∑ j, intrinsicRealPrincipal A p x i j*
      Yau.coordPartial (fun y ↦ Yau.coordPartial (w ∘ sphereChartCoordMap p) y j) x i) =
      -((∑ j, intrinsicRealDrift A p x j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j) +
        intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)) := by
    linarith only [heq]
  rw [hid,abs_neg]
  calc
    _ ≤ |∑ j, intrinsicRealDrift A p x j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j| +
        |intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)| := abs_add_le _ _
    _ ≤ (∑ j, |intrinsicRealDrift A p x j*Yau.coordPartial (w ∘ sphereChartCoordMap p) x j|) +
        |intrinsicRealPotential rho lam p x*w (sphereChartCoordMap p x)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
    _ ≤ (∑ j, C*|Yau.coordPartial (w ∘ sphereChartCoordMap p) x j|) +
        C*|w (sphereChartCoordMap p x)| := by
      simp only [abs_mul]
      exact add_le_add (Finset.sum_le_sum (fun j _ ↦
        mul_le_mul_of_nonneg_right ((hb x hx).2 j) (abs_nonneg _)))
        (mul_le_mul_of_nonneg_right (hb x hx).1 (abs_nonneg _))
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end Yau.Target

end OAI
