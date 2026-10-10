import OAI.Geometry.CylinderCovering.Ruled.Retention

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace RuledApproximation.OrthogonalRetention

lemma volume_toLp_image (S : Set (Fin 2 → ℝ)) :
    volume (WithLp.toLp 2 '' S : Set Plane) = volume S := by
  have he := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph.measurableEmbedding.map_apply
    volume (WithLp.toLp 2 '' S)
  have hm := (PiLp.volume_preserving_toLp (Fin 2)).map_eq
  change Measure.map (WithLp.toLp 2) volume (WithLp.toLp 2 '' S) =
    volume (WithLp.toLp 2 ⁻¹' (WithLp.toLp 2 '' S)) at he
  rw [hm, Set.preimage_image_eq S (WithLp.toLp_injective 2)] at he
  exact he

lemma volume_orthogonal_image (R : Plane ≃ₗᵢ[ℝ] Plane) (S : Set Plane) :
    volume (R '' S) = volume S := by
  have he := R.toHomeomorph.measurableEmbedding.map_apply volume (R '' S)
  change Measure.map R volume (R '' S) = volume (R ⁻¹' (R '' S)) at he
  rw [R.measurePreserving.map_eq, Set.preimage_image_eq S R.injective] at he
  exact he

lemma volume_translation_image (p : Plane) (S : Set Plane) :
    volume ((fun x => p + x) '' S) = volume S := by
  have he := (Homeomorph.addLeft p).measurableEmbedding.map_apply volume ((fun x => p + x) '' S)
  change Measure.map (fun x => p + x) volume ((fun x => p + x) '' S) =
    volume ((fun x => p + x) ⁻¹' ((fun x => p + x) '' S)) at he
  rw [(measurePreserving_add_left volume p).map_eq,
    Set.preimage_image_eq S (fun _ _ h => add_left_cancel h)] at he
  exact he

lemma unitSquare_volume : volume unitSquare = 1 := by
  have he : unitSquare = WithLp.toLp 2 ''
      (Set.univ.pi (fun _ : Fin 2 => Icc (- (1 / 2 : ℝ)) (1 / 2))) := by
    ext x
    constructor
    · intro hx
      refine ⟨WithLp.ofLp x, ?_, rfl⟩
      intro i _
      exact abs_le.mp (hx i)
    · rintro ⟨y, hy, rfl⟩
      intro i
      exact abs_le.mpr (hy i (Set.mem_univ i))
  rw [he, volume_toLp_image, volume_pi_pi]
  norm_num [Real.volume_Icc]

lemma square_volume (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (ell : ℝ)
    (ij : ℤ × ℤ) : volume (square p R ell ij) = ENNReal.ofReal (ell ^ 2) := by
  have he : square p R ell ij =
      (fun x => center p R ell ij + x) '' (ell • (R '' unitSquare)) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ell • R u, ⟨R u, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
  rw [he, volume_translation_image, Measure.addHaar_smul, volume_orthogonal_image,
    unitSquare_volume, mul_one]
  simp [finrank_euclideanSpace, abs_of_nonneg (sq_nonneg ell)]

lemma square_area (p : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (ell : ℝ)
    (ij : ℤ × ℤ) : volume.real (square p R ell ij) = ell ^ 2 := by
  rw [measureReal_def, square_volume, ENNReal.toReal_ofReal (sq_nonneg ell)]

lemma physicalFamily_area_exact {h : ℝ} (hh : 0 < h) (p v₀ : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (A : Plane →L[ℝ] Plane) (ell : ℝ)
    (F : Finset (ℤ × ℤ)) (i : Fin F.card) :
    (physicalFamily h p v₀ R A ell F i).area = h * ell ^ 2 *
      physicalWeight h (affineVelocity p v₀ A (center p R ell (F.equivFin.symm i))) := by
  rw [physicalFamily_area hh, square_area]

end RuledApproximation.OrthogonalRetention

end

end OAI
