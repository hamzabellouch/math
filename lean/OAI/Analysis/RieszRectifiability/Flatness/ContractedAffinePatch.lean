import Mathlib
import OAI.Analysis.RieszRectifiability.Projections.NonemptyAffineProjectionIncrement
import OAI.Analysis.RieszRectifiability.Flatness.ContractedDirectionTube

namespace OAI

/-!
Failure of a lower norm bound produces a contracted unit direction. Translating an affine patch
into a linear tube then gives a mass estimate for its image under the contracting map.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set EuclideanGeometry

theorem exists_contracted_unit_direction_of_not_lower {d e : ℕ}
    (S : Submodule ℝ (Ambient d)) (T : Ambient d →ₗ[ℝ] Ambient e) (κ : ℝ)
    (hnot : ¬ ∀ v : S, κ * ‖v‖ ≤ ‖T (v : Ambient d)‖) :
    ∃ u : S, ‖u‖ = 1 ∧ ‖T (u : Ambient d)‖ < κ := by
  push Not at hnot
  obtain ⟨v, hv⟩ := hnot
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  let u : S := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs]
    change |‖v‖⁻¹| * ‖v‖ = 1
    rw [abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  refine ⟨u, hu, ?_⟩
  change ‖T (‖v‖⁻¹ • (v : Ambient d))‖ < κ
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  have h := mul_lt_mul_of_pos_left hv (inv_pos.mpr hn)
  simpa only [← mul_assoc, inv_mul_cancel_left₀ hn.ne', mul_comm κ] using! h

theorem infDist_translated_affine_direction {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (b : Ambient d) (hb : b ∈ S) (x : Ambient d) :
    infDist (x - b) (S.direction : Set (Ambient d)) = infDist x (S : Set (Ambient d)) := by
  have hp := affine_projection_difference S x b
  rw [orthogonalProjection_eq_self_iff.mpr hb] at hp
  have hn : (x - b) - S.direction.starProjection (x - b) =
      (S.directionᗮ : Submodule ℝ (Ambient d)).starProjection (x - b) := by
    have h := S.direction.starProjection_add_starProjection_orthogonal (x - b)
    exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
  rw [submodule_infDist_eq_normal_projection, ← hn, ← hp, sub_sub_sub_cancel_right]
  exact (dist_orthogonalProjection_eq_infDist S x)

theorem translated_affine_patch_subset_tube {d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) [Nonempty S]
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ) :
    (fun x => x - b) '' A ⊆ affineTube S.direction.toAffineSubspace R δ := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · change dist (x - b) 0 ≤ R
    rw [dist_zero_right, ← dist_eq_norm]
    exact (dist_triangle x c b).trans ((add_le_add (hA hx) hcenter).trans hrad)
  · change infDist (x - b) (S.direction : Set (Ambient d)) < δ
    rw [infDist_translated_affine_direction S b hb x]
    exact hheight x hx

theorem contracted_affine_patch_translated_real_measure_bound {n d : ℕ}
    (S : AffineSubspace ℝ (Ambient d)) (hS : IsAffineNPlane n S)
    (T : Ambient d →ₗ[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (u : S.direction) (hu : ‖u‖ = 1) (κ : ℝ) (hκ : 0 ≤ κ)
    (hTu : ‖T (u : Ambient d)‖ ≤ κ)
    (μ : Measure (Ambient n)) (C : ℝ) (hg : GlobalUpperGrowth n C μ)
    (b c : Ambient d) (hb : b ∈ S) (A : Set (Ambient d)) (r a R δ : ℝ)
    (hA : A ⊆ closedBall c r) (hcenter : dist c b ≤ a) (hrad : r + a ≤ R)
    (hheight : ∀ x ∈ A, infDist x (S : Set (Ambient d)) < δ)
    (hR : 0 < R) (hδ : 0 < δ) (hwidth : δ + κ * R ≤ R) :
    μ.real ((fun x => T (x - b)) '' A) ≤
      (C * (2 : ℝ) ^ n * (3 : ℝ) ^ n) * ((δ + κ * R) / R) * R ^ n := by
  let : Nonempty S := hS.1.to_subtype
  have hsub : (fun x => T (x - b)) '' A ⊆
      T '' affineTube S.direction.toAffineSubspace R δ := by
    rw [← Set.image_image]
    exact Set.image_mono (translated_affine_patch_subset_tube S b c hb A r a R δ
      hA hcenter hrad hheight)
  have hball : T '' affineTube S.direction.toAffineSubspace R δ ⊆ ball 0 (2 * R) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using! hx.1
    rw [mem_ball, dist_zero_right]
    exact (hT x).trans_lt (by linarith)
  have hfinite : μ (T '' affineTube S.direction.toAffineSubspace R δ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hball).trans (hg.2 0 (2 * R) (by positivity)))
  exact (ENNReal.toReal_mono hfinite (measure_mono hsub)).trans
    (contracted_plane_tube_image_real_measure_bound S.direction hS.2 T hT u hu
      κ hκ hTu μ C hg R δ hR hδ hwidth)

end

end RieszRectifiability

end OAI
