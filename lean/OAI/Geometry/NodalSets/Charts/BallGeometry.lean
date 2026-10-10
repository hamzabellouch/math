import OAI.Geometry.NodalSets.Charts.MetricFrequencyBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
noncomputable section

lemma sourceEuclideanNorm_eq_norm (x : Coord) :
    sourceEuclideanNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 4))‖ := by
  simp only [EuclideanSpace.norm_eq,Real.norm_eq_abs,sq_abs,sourceEuclideanNorm]

lemma sourceEuclideanNorm_add_le (x y : Coord) :
    sourceEuclideanNorm (x+y) ≤ sourceEuclideanNorm x+sourceEuclideanNorm y := by
  simp_rw [sourceEuclideanNorm_eq_norm]
  exact norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

lemma sourceEuclideanNorm_single (j : Fin 4) (t : ℝ) :
    sourceEuclideanNorm (t • Pi.single j (1:ℝ)) = |t| := by
  rw [sourceEuclideanNorm_smul]
  simp [sourceEuclideanNorm,Pi.single_apply]

lemma sourceEuclideanBall_compact (R : ℝ) : IsCompact {x : Coord | sourceEuclideanNorm x ≤ R} := by
  have he : {x : Coord | sourceEuclideanNorm x ≤ R} =
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)) '' closedBall 0 R := by
    ext x
    simp only [mem_ofPred_eq,mem_image,mem_closedBall,dist_zero_right]
    constructor
    · intro hx
      exact ⟨WithLp.toLp 2 x,by rwa [← sourceEuclideanNorm_eq_norm],rfl⟩
    · rintro ⟨y,hy,rfl⟩
      rw [sourceEuclideanNorm_eq_norm]
      change ‖(WithLp.toLp 2 y.ofLp : EuclideanSpace ℝ (Fin 4))‖ ≤ R
      simpa only [WithLp.toLp_ofLp] using hy
  rw [he]
  exact (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).image
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 ↦ ℝ)).continuous

lemma sourceEuclideanBall_convex (R : ℝ) : Convex ℝ {x : Coord | sourceEuclideanNorm x ≤ R} := by
  intro x hx y hy a b ha hb hab
  change sourceEuclideanNorm (a • x+b • y) ≤ R
  apply (sourceEuclideanNorm_add_le _ _).trans
  rw [sourceEuclideanNorm_smul,sourceEuclideanNorm_smul,abs_of_nonneg ha,abs_of_nonneg hb]
  calc
    _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul,hab,one_mul]

lemma source_sign_subballs_inside {tau r : ℝ} (ht : 0 ≤ tau) (_hr : 0 ≤ r)
    (htr : tau+r ≤ 1) (j : Fin 4) :
    (∀ v : Coord, sourceEuclideanNorm v ≤ r → sourceEuclideanNorm v ≤ 1) ∧
    (∀ v : Coord, sourceEuclideanNorm (v-tau • Pi.single j 1) ≤ r →
      sourceEuclideanNorm v ≤ 1) := by
  constructor
  · intro v hv
    linarith
  · intro v hv
    have hh := sourceEuclideanNorm_add_le (v-tau • Pi.single j 1) (tau • Pi.single j 1)
    rw [sub_add_cancel,sourceEuclideanNorm_single,abs_of_nonneg ht] at hh
    linarith

end
end Yau.Geometry

end OAI
