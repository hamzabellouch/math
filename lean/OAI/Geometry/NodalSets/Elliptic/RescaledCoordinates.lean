import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Elliptic.CoordinateNorm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

lemma rescaling_radius_bound {N s : ℝ} (hN : 1 ≤ N) (hs : 1 ≤ s) :
    0 ≤ (N*s)⁻¹ ∧ (N*s)⁻¹ ≤ 1 ∧ N*(N*s)⁻¹ ≤ 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  refine ⟨by positivity,(inv_le_one₀ (mul_pos hN0 hs0)).mpr
    (one_le_mul_of_one_le_of_one_le hN hs),?_⟩
  have he : N*(N*s)⁻¹ = s⁻¹ := by field_simp
  rw [he]
  exact (inv_le_one₀ hs0).mpr hs

theorem compact_rescaled_envelope_bound (S : Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    {Q : Set Coord} (hQ : IsCompact Q) (R : ℝ) (hR : 0 ≤ R) :
    ∃ L > 0, ∀ (N s : ℝ), 1 ≤ N → 1 ≤ s → ∀ x ∈ Q,
      ∀ v : Coord, ‖v‖ ≤ R →
        |N*(S (x+(N*s)⁻¹ • v)-S x)| ≤ L := by
  obtain ⟨B,hB,hBQ⟩ := hQ.isBounded.exists_pos_norm_le
  let P := Metric.closedBall (0:Coord) (B+R+1)
  have hP : IsCompact P := isCompact_closedBall _ _
  obtain ⟨A,hA,hAP⟩ := (hP.image (hS.continuous_fderiv (by simp))).isBounded.exists_pos_norm_le
  refine ⟨A*(R+1),by positivity,?_⟩
  intro N s hN hs x hx v hv
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  obtain ⟨hr0,hr1,hNr⟩ := rescaling_radius_bound hN hs
  have hxP : x ∈ P := by
    change dist x 0 ≤ B+R+1
    rw [dist_zero_right]
    linarith [hBQ x hx]
  have hd : ‖(x+(N*s)⁻¹ • v)-x‖ = (N*s)⁻¹*‖v‖ := by
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hr0]
  have hzP : x+(N*s)⁻¹ • v ∈ P := by
    change dist (x+(N*s)⁻¹ • v) 0 ≤ B+R+1
    rw [dist_zero_right]
    have ht := norm_le_norm_sub_add (x+(N*s)⁻¹ • v) x
    rw [hd] at ht
    have hb : (N*s)⁻¹*‖v‖ ≤ R :=
      (mul_le_mul_of_nonneg_right hr1 (norm_nonneg _)).trans (by simpa using hv)
    linarith [hBQ x hx]
  have h := (convex_closedBall (0:Coord) (B+R+1)).norm_image_sub_le_of_norm_fderiv_le
    (fun _ _ ↦ (hS.differentiable (by simp)).differentiableAt)
    (fun y hy ↦ hAP _ ⟨y,hy,rfl⟩) hxP hzP
  rw [hd] at h
  change |S (x+(N*s)⁻¹ • v)-S x| ≤ A*((N*s)⁻¹*‖v‖) at h
  rw [abs_mul,abs_of_pos hN0]
  calc
    _ ≤ N*(A*((N*s)⁻¹*‖v‖)) := mul_le_mul_of_nonneg_left h hN0.le
    _ = A*(N*(N*s)⁻¹)*‖v‖ := by ring
    _ ≤ A*1*R := by gcongr
    _ ≤ _ := by nlinarith

end
end Yau.Geometry

end OAI
