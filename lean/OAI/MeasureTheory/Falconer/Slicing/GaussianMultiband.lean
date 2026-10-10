import OAI.MeasureTheory.Falconer.Slicing.GaussianBox

namespace OAI

/-! # Gaussian multi-vector bands with their exact coordinate determinant -/

namespace Falconer
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {d j : ℕ}

noncomputable def bandCoordinateMap (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) : Space j →L[ℝ] Space j :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin j => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (innerSL ℝ (w i)).comp
      (V.subtypeL.comp b.symm.toContinuousLinearEquiv.toContinuousLinearMap)))

@[simp] theorem bandCoordinateMap_apply (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) (x : Space j) (i : Fin j) :
    bandCoordinateMap w V b x i = inner ℝ (w i) (b.symm x : Space d) := rfl

theorem bandCoordinateMap_det_ne_zero (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hspan : Submodule.span ℝ (range w) = V) (b : V ≃ₗᵢ[ℝ] Space j) :
    LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j) ≠ 0 := by
  rw [ne_eq,LinearMap.det_eq_zero_iff_ker_ne_bot,not_not]
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hi (i : Fin j) : inner ℝ (w i) (b.symm x : Space d) = 0 := by
    have hh := congrArg (fun z : Space j => z i) hx
    simpa using hh
  have hall (u : Space d) (hu : u ∈ Submodule.span ℝ (range w)) :
      inner ℝ u (b.symm x : Space d) = 0 := by
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i,rfl⟩ := hu; exact hi i
    | zero => simp
    | add u v hu hv ihu ihv => simp [inner_add_left,ihu,ihv]
    | smul a u hu ihu => simp [inner_smul_left,ihu]
  have hy : (b.symm x : Space d) = 0 := inner_self_eq_zero.mp
    (hall _ (by rw [hspan]; exact (b.symm x).property))
  have hz : b.symm x = 0 := Subtype.ext hy
  exact b.symm.injective (by simpa using hz)

theorem gaussian_projected_coordinates (V : Submodule ℝ (Space d))
    (b : V ≃ₗᵢ[ℝ] Space j) :
    (stdGaussian (Space d)).map (fun x => b (V.orthogonalProjectionOnto x)) =
      stdGaussian (Space j) := by
  change (stdGaussian (Space d)).map (b ∘ V.orthogonalProjectionOnto) = _
  rw [← Measure.map_map b.continuous.measurable V.orthogonalProjectionOnto.continuous.measurable,
    gaussian_orthogonal_projection,stdGaussian_map]

theorem gaussian_multi_vector_band (w : Fin j → Space d) (V : Submodule ℝ (Space d))
    (hw : ∀ i, w i ∈ V) (b : V ≃ₗᵢ[ℝ] Space j)
    (hdet : LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j) ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space d) {x | ∀ i, |inner ℝ (w i) x| ≤ r} ≤
      ENNReal.ofReal (gaussianVolumeNormalization j*
        |(LinearMap.det (bandCoordinateMap w V b : Space j →ₗ[ℝ] Space j))⁻¹| * (2*r)^j) := by
  let F : Space d → Space j := fun x => b (V.orthogonalProjectionOnto x)
  have he : {x : Space d | ∀ i, |inner ℝ (w i) x| ≤ r} =
      F ⁻¹' {y : Space j | ∀ i, |bandCoordinateMap w V b y i| ≤ r} := by
    ext x
    simp only [mem_preimage,mem_ofPred_eq,F,bandCoordinateMap_apply,b.symm_apply_apply]
    have hi (i : Fin j) : inner ℝ (w i) (V.orthogonalProjectionOnto x : Space d) =
        inner ℝ (w i) x :=
      V.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨w i,hw i⟩ x
    simp only [hi]
  rw [he,← Measure.map_apply (by dsimp [F]; fun_prop) (by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact measurableSet_le (by fun_prop) measurable_const),gaussian_projected_coordinates]
  exact gaussian_linear_bands _ hdet hr

end Falconer

end OAI
