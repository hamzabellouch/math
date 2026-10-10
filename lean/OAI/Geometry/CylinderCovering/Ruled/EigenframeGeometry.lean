import OAI.Geometry.CylinderCovering.Ruled.LocalEndpoint

namespace OAI

noncomputable section
open Set
namespace CylinderCovering.ProductLocal
open RuledApproximation

def euclideanFrame62a5 (L : (ℝ × ℝ) ≃L[ℝ] Plane) : Plane →L[ℝ] Plane :=
  matrixCLM (L (1, 0) 0) (L (0, 1) 0) (L (1, 0) 1) (L (0, 1) 1)

lemma euclideanFrame62a5_apply (L : (ℝ × ℝ) ≃L[ℝ] Plane) (z : Plane) :
    euclideanFrame62a5 L z = L (z 0, z 1) := by
  rw [frame_apply]
  ext i
  fin_cases i <;> simp [euclideanFrame62a5, matrixCLM, vec2] <;> ring

lemma euclideanFrame62a5_det (L : (ℝ × ℝ) ≃L[ℝ] Plane) :
    LinearMap.det (euclideanFrame62a5 L).toLinearMap =
      L (1, 0) 0 * L (0, 1) 1 - L (0, 1) 0 * L (1, 0) 1 := by
  exact matrixCLM_det _ _ _ _

lemma abs_sum_le_sqrt_two_norm62a5 (z : Plane) :
    |z 0| + |z 1| ≤ Real.sqrt 2 * ‖z‖ := by
  have hn := plane_norm_sq z
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hprod : (Real.sqrt 2 * ‖z‖) ^ 2 = 2 * (z 0 ^ 2 + z 1 ^ 2) := by
    rw [mul_pow, hs, hn]
  nlinarith [sq_nonneg (|z 0| - |z 1|), sq_abs (z 0), sq_abs (z 1),
    abs_nonneg (z 0), abs_nonneg (z 1),
    mul_nonneg (Real.sqrt_nonneg (2 : ℝ)) (norm_nonneg z)]

theorem euclideanFrame62a5_norm {A : Plane →L[ℝ] Plane} {lam : ℝ}
    {L : (ℝ × ℝ) ≃L[ℝ] Plane} (hL : IsUnitEigenframe A lam L) :
    ‖euclideanFrame62a5 L‖ ≤ Real.sqrt 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro z
  rw [euclideanFrame62a5_apply]
  exact (frame_norm_le hL (z 0, z 1)).trans (abs_sum_le_sqrt_two_norm62a5 z)

theorem euclideanFrame62a5_det_lower {A : Plane →L[ℝ] Plane} {lam N : ℝ}
    {L : (ℝ × ℝ) ≃L[ℝ] Plane} (hL : IsUnitEigenframe A lam L)
    (hN : 0 < N) (hbound : ∀ z : Plane, ‖L.symm z‖ ≤ N * ‖z‖) :
    1 / (2 * N) ≤ |LinearMap.det (euclideanFrame62a5 L).toLinearMap| := by
  let v := L (1, 0)
  let w := L (0, 1)
  let d := v 0 * w 1 - w 0 * v 1
  have hfirst : L (w 1, -(v 1)) = vec2 d 0 := by
    rw [frame_apply]
    ext i
    fin_cases i <;> simp [v, w, d, vec2] <;> ring
  have hsecond : L (w 0, -(v 0)) = vec2 0 (-d) := by
    rw [frame_apply]
    ext i
    fin_cases i <;> simp [v, w, d, vec2] <;> ring
  have hw1 : |w 1| ≤ N * |d| := by
    have hb := hbound (vec2 d 0)
    rw [← hfirst, L.symm_apply_apply] at hb
    rw [hfirst] at hb
    have hc : |w 1| ≤ ‖(w 1, -(v 1))‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (w 1, -(v 1))
    exact (hc.trans hb).trans_eq (by simp [vec2, EuclideanSpace.norm_eq,
      Real.sqrt_sq_eq_abs])
  have hw0 : |w 0| ≤ N * |d| := by
    have hb := hbound (vec2 0 (-d))
    rw [← hsecond, L.symm_apply_apply] at hb
    rw [hsecond] at hb
    have hc : |w 0| ≤ ‖(w 0, -(v 0))‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (w 0, -(v 0))
    exact (hc.trans hb).trans_eq (by simp [vec2, EuclideanSpace.norm_eq,
      Real.sqrt_sq_eq_abs])
  have hw : ‖w‖ = 1 := hL.2.1
  have hs := plane_norm_le_sum w
  rw [hw] at hs
  rw [euclideanFrame62a5_det]
  change 1 / (2 * N) ≤ |d|
  apply (div_le_iff₀ (by positivity : 0 < 2 * N)).mpr
  nlinarith

theorem compact_uniform_euclidean_frame_geometry62a5
    {X : Type*} [TopologicalSpace X] {D : Set X} (hD : IsCompact D)
    {A : X → Plane →L[ℝ] Plane} (hA : ContinuousOn A D)
    (htr : ∀ p ∈ D, LinearMap.trace ℝ Plane (A p).toLinearMap = 0)
    (hdet : ∀ p ∈ D, LinearMap.det (A p).toLinearMap < 0) :
    ∃ β N : ℝ, 0 < β ∧ 0 < N ∧
      ∀ p ∈ D, ∀ lam : ℝ, ∀ L : (ℝ × ℝ) ≃L[ℝ] Plane,
        0 < lam → IsUnitEigenframe (A p) lam L →
        β ≤ |LinearMap.det (euclideanFrame62a5 L).toLinearMap| ∧
        ‖euclideanFrame62a5 L‖ ≤ Real.sqrt 2 ∧
        ∀ z : Plane, ‖vec2 (L.symm z).1 (L.symm z).2‖ ≤ N * ‖z‖ := by
  obtain ⟨N, hN, hbound⟩ := compact_uniform_eigenframe_inverse hD hA htr hdet
  refine ⟨1 / (2 * N), 2 * N, by positivity, by positivity, ?_⟩
  intro p hp lam L hlam hL
  have hb := (hbound p hp lam L hlam hL).2
  refine ⟨euclideanFrame62a5_det_lower hL hN hb, euclideanFrame62a5_norm hL, ?_⟩
  intro z
  have h0 : |(L.symm z).1| ≤ ‖L.symm z‖ := by
    simpa only [Real.norm_eq_abs] using norm_fst_le (L.symm z)
  have h1 : |(L.symm z).2| ≤ ‖L.symm z‖ := by
    simpa only [Real.norm_eq_abs] using norm_snd_le (L.symm z)
  have hs := plane_norm_le_sum (vec2 (L.symm z).1 (L.symm z).2)
  simp only [vec2_apply_zero, vec2_apply_one] at hs
  nlinarith [hb z]

end CylinderCovering.ProductLocal

end

end OAI
