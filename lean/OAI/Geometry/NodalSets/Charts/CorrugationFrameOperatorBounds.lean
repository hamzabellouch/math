import OAI.Geometry.NodalSets.Charts.CorrugationFrameBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets
noncomputable section

lemma frozenFrame_operator_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c : ℝ} (hc : 0 < c) (hg : ∀ v : Coord, c*‖v‖^2 ≤ g v v)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (v : Coord) : ‖e v‖ ≤ (4*(1+c⁻¹))*‖v‖ := by
  have hv : v = ∑ i : Fin 4, v i • Pi.single i (1:ℝ) := by
    ext j
    simp [Pi.single_apply,Finset.sum_apply]
  have hu : ∀ i : Fin 4, ‖e (Pi.single i 1)‖ ≤ 1+c⁻¹ :=
    fun i ↦ metric_unit_coordinate_bound g hc hg _ (by simpa using he i i)
  calc
    ‖e v‖ = ‖∑ i : Fin 4, v i • e (Pi.single i 1)‖ := by conv_lhs => rw [hv,map_sum]; simp only [map_smul]
    _ ≤ ∑ i : Fin 4, ‖v i • e (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 4, ‖v‖*(1+c⁻¹) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (hu i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp; ring

lemma frozenFrame_inverse_operator_bound (g : Coord →L[ℝ] Coord →L[ℝ] ℝ)
    {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hg : ∀ v : Coord, c*‖v‖^2 ≤ g v v) (hupper : ‖g‖ ≤ M)
    (e : Coord ≃L[ℝ] Coord)
    (he : ∀ i j, g (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0)
    (v : Coord) : ‖e.symm v‖ ≤ (M*(1+c⁻¹))*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  exact ((frozenFrameCovector e i).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (frozenFrameCovector_norm_bound g hc hM hg hupper e he i) (norm_nonneg v))

end
end Yau.Geometry

end OAI
