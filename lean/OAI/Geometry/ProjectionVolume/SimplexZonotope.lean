import OAI.Geometry.ProjectionVolume.Basic
import OAI.Geometry.ProjectionVolume.SupportGeometry
import OAI.Geometry.ProjectionVolume.EuclideanVolume

namespace OAI

universe uE uι

open Set MeasureTheory
open scoped Pointwise RealInnerProductSpace

namespace Paper092

noncomputable def simplexZonotope (d : ℕ) : Set (Euclidean d) :=
  (∑ i : Fin d, segment ℝ
    (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))
    ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))) +
  segment ℝ
    (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • WithLp.toLp 2 (1 : Fin d → ℝ)))
    ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • WithLp.toLp 2 (1 : Fin d → ℝ)))

theorem simplexZonotope_isCompact (d : ℕ) : IsCompact (simplexZonotope d) := by
  unfold simplexZonotope
  exact (Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
    isCompact_singleton (fun _ _ => SupportGeometry.isCompact_segment _ _)).add
      (SupportGeometry.isCompact_segment _ _)

theorem simplexZonotope_nonempty (d : ℕ) : (simplexZonotope d).Nonempty := by
  unfold simplexZonotope
  exact (Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
    (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)).add
      ⟨_, left_mem_segment ℝ _ _⟩

theorem simplexZonotope_convex (d : ℕ) : Convex ℝ (simplexZonotope d) := by
  unfold simplexZonotope
  exact (convex_sum _ (fun _ _ => convex_segment _ _)).add (convex_segment _ _)

theorem simplexZonotope_support (d : ℕ) (u : Euclidean d) :
    SupportGeometry.support (simplexZonotope d) (innerSL ℝ u) =
      ((∑ i : Fin d, |u i|) + |∑ i : Fin d, u i|) / (2 * ((d - 1).factorial : ℝ)) := by
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  have hcompact : IsCompact (∑ i : Fin d, segment ℝ
      (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))) :=
    Finset.sum_induction _ IsCompact (fun _ _ ha hb => ha.add hb)
      isCompact_singleton (fun _ _ => SupportGeometry.isCompact_segment _ _)
  have hne : (∑ i : Fin d, segment ℝ
      (-(1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (((d - 1).factorial : ℝ)⁻¹ • EuclideanSpace.single i (1 : ℝ)))).Nonempty :=
    Finset.sum_induction _ Set.Nonempty (fun _ _ ha hb => ha.add hb)
      (singleton_nonempty 0) (fun _ _ => ⟨_, left_mem_segment ℝ _ _⟩)
  rw [simplexZonotope, SupportGeometry.support_add hcompact hne
    (SupportGeometry.isCompact_segment _ _) ⟨_, left_mem_segment ℝ _ _⟩,
    SupportGeometry.support_sum_centered_segments, SupportGeometry.support_centered_segment]
  simp only [innerSL_apply_apply, inner_smul_right, EuclideanSpace.inner_single_right,
    one_mul, starRingEnd_apply, star_trivial, abs_mul, abs_inv, abs_of_pos hfac]
  have hw : inner ℝ u (WithLp.toLp 2 (1 : Fin d → ℝ)) = ∑ i : Fin d, u i := by
    simp [PiLp.inner_apply]
  rw [hw, ← Finset.mul_sum]
  field_simp

theorem centered_segment_eq_vadd {E : Type uE} [AddCommGroup E] [Module ℝ E] (v : E) :
    segment ℝ (-(1 / 2 : ℝ) • v) ((1 / 2 : ℝ) • v) =
      (-(1 / 2 : ℝ) • v) +ᵥ segment ℝ 0 v := by
  rw [vadd_segment]
  simp only [vadd_eq_add, add_zero]
  congr 1
  symm
  simpa only [add_smul, one_smul] using
    congrArg (fun a : ℝ => a • v) (by norm_num : -(1 / 2 : ℝ) + 1 = 1 / 2)

theorem sum_centered_segments_eq_vadd {ι : Type uι} {E : Type uE} [Fintype ι] [AddCommGroup E]
    [Module ℝ E] (v : ι → E) :
    (∑ i, segment ℝ (-(1 / 2 : ℝ) • v i) ((1 / 2 : ℝ) • v i)) =
      (-(1 / 2 : ℝ) • ∑ i, v i) +ᵥ parallelepiped v := by
  simp_rw [centered_segment_eq_vadd, ← image_vadd, vadd_eq_add, ← singleton_add]
  rw [Finset.sum_add_distrib, Set.finsetSum_singleton, ← Finset.smul_sum,
    ← parallelepiped_eq_sum_segment]

theorem coordinate_segments_eq_cube (d : ℕ) :
    (∑ i : Fin d, segment ℝ (0 : Euclidean d) (EuclideanSpace.single i (1 : ℝ))) =
      WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1 := by
  rw [← parallelepiped_eq_sum_segment, parallelepiped]
  congr 1
  funext t
  ext j
  simp [WithLp.ofLp_sum, Pi.single_apply]

theorem smul_segment_image {E : Type uE} [AddCommGroup E] [Module ℝ E]
    (r : ℝ) (x y : E) : r • segment ℝ x y = segment ℝ (r • x) (r • y) :=
  image_segment ℝ (r • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap x y

theorem simplexZonotope_eq_vadd_smul (d : ℕ) :
    simplexZonotope d =
      -(((d - 1).factorial : ℝ)⁻¹ • WithLp.toLp 2 (1 : Fin d → ℝ)) +ᵥ
      (((d - 1).factorial : ℝ)⁻¹ •
        ((WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) +
          segment ℝ (0 : Euclidean d) (WithLp.toLp 2 (1 : Fin d → ℝ)))) := by
  let r : ℝ := ((d - 1).factorial : ℝ)⁻¹
  let w : Euclidean d := WithLp.toLp 2 (1 : Fin d → ℝ)
  have hsum : (∑ i : Fin d, EuclideanSpace.single i (1 : ℝ)) = w := by
    ext j
    simp [w, WithLp.ofLp_sum, Pi.single_apply]
  have hpara : parallelepiped (fun i : Fin d => r • EuclideanSpace.single i (1 : ℝ)) =
      r • (WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1) := by
    rw [parallelepiped_eq_sum_segment, ← coordinate_segments_eq_cube,
      Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_segment_image, smul_zero]
  change (∑ i : Fin d, segment ℝ (-(1 / 2 : ℝ) • (r • EuclideanSpace.single i (1 : ℝ)))
      ((1 / 2 : ℝ) • (r • EuclideanSpace.single i (1 : ℝ)))) +
      segment ℝ (-(1 / 2 : ℝ) • (r • w)) ((1 / 2 : ℝ) • (r • w)) = _
  rw [sum_centered_segments_eq_vadd, ← Finset.smul_sum, hsum,
    centered_segment_eq_vadd, hpara]
  have hseg : segment ℝ (0 : Euclidean d) (r • w) = r • segment ℝ 0 w := by
    rw [smul_segment_image, smul_zero]
  rw [hseg]
  simp_rw [← image_vadd, vadd_eq_add, ← singleton_add]
  rw [add_add_add_comm, singleton_add_singleton,
    ← smul_add r (WithLp.toLp 2 '' Icc (0 : Fin d → ℝ) 1)
      (segment ℝ (0 : Euclidean d) w)]
  congr 2
  calc
    -(1 / 2 : ℝ) • (r • w) + -(1 / 2 : ℝ) • (r • w) =
        (-1 : ℝ) • (r • w) := by rw [← add_smul]; norm_num
    _ = -(r • w) := neg_one_smul ℝ _

theorem volume_simplexZonotope (d : ℕ) (hd : 0 < d) :
    volume (simplexZonotope d) =
      ENNReal.ofReal (((d : ℝ) + 1) / (((d - 1).factorial : ℝ) ^ d)) := by
  have hfac : (0 : ℝ) < (d - 1).factorial := by exact_mod_cast Nat.factorial_pos (d - 1)
  rw [simplexZonotope_eq_vadd_smul, measure_vadd, Measure.addHaar_smul,
    finrank_euclideanSpace_fin, volume_euclidean_cube_add_diagonal d hd]
  rw [abs_pow, abs_inv, abs_of_pos hfac]
  rw [ENNReal.ofReal_div_of_pos (pow_pos hfac d)]
  simp [inv_pow, div_eq_mul_inv, mul_comm,
    ENNReal.ofReal_add (Nat.cast_nonneg d) zero_le_one,
    ENNReal.ofReal_pow hfac.le, ENNReal.ofReal_inv_of_pos (pow_pos hfac d)]

theorem simplexZonotope_volume (d : ℕ) (hd : 0 < d) :
    (volume (simplexZonotope d)).toReal =
      ((d : ℝ) + 1) / (((d - 1).factorial : ℝ) ^ d) := by
  rw [volume_simplexZonotope d hd, ENNReal.toReal_ofReal]
  positivity

end Paper092

end OAI
