import OAI.Geometry.Zonotope.Shear
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DiagonalZonotope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma cube_eq_pi : (cube : Set (ι → ℝ)) = Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

omit [Fintype ι] [DecidableEq ι] in
lemma isCompact_cube : IsCompact (cube : Set (ι → ℝ)) := by
  rw [cube_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

omit [Fintype ι] in
lemma continuous_extrusionMap (i : ι) : Continuous (extrusionMap i : (ι → ℝ) → (ι → ℝ)) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · simpa [extrusionMap, hji] using (show Continuous (fun a : ι → ℝ => (1 : ℝ) + a i) from
      continuous_const.add (continuous_apply i))
  · simpa [extrusionMap, hji] using (show Continuous (fun a : ι → ℝ => a j + a i) from
      (continuous_apply j).add (continuous_apply i))

omit [Fintype ι] in
lemma isCompact_cell (i : ι) : IsCompact (cell i) := by
  rw [cell_eq_image_cube]
  exact isCompact_cube.image (continuous_extrusionMap i)

omit [DecidableEq ι] in
@[simp] theorem volume_cube : volume (cube : Set (ι → ℝ)) = 1 := by
  rw [cube_eq_pi, volume_pi_pi]
  simp

@[simp] theorem volume_cell (i : ι) : volume (cell i) = 1 := by
  rw [cell_eq_image_cube]
  have hmap : extrusionMap i = (fun y : ι → ℝ => Pi.single i 1 + y) ∘ shear i := by
    funext s
    exact extrusionMap_eq i s
  rw [hmap, Set.image_comp]
  rw [image_add_left, measure_preimage_add]
  rw [Measure.addHaar_image_linearMap, shear_det, volume_cube]
  simp

omit [DecidableEq ι] in
lemma volume_coordinate_hyperplane (i : ι) (r : ℝ) :
    volume {x : ι → ℝ | x i = r} = 0 := by
  exact Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i r

lemma volume_coordinate_diagonal {i j : ι} (hij : i ≠ j) :
    volume {x : ι → ℝ | x i = x j} = 0 := by
  let H : Submodule ℝ (ι → ℝ) :=
    { carrier := {x | x i = x j}
      zero_mem' := rfl
      add_mem' := by
        intro x y hx hy
        exact congrArg₂ (· + ·) hx hy
      smul_mem' := by
        intro c x hx
        exact congrArg (fun t : ℝ => c * t) hx }
  change volume (H : Set (ι → ℝ)) = 0
  apply Measure.addHaar_submodule
  intro htop
  have hmem : Pi.single i (1 : ℝ) ∈ H := by
    rw [htop]
    trivial
  change (Pi.single i (1 : ℝ) : ι → ℝ) i = (Pi.single i (1 : ℝ) : ι → ℝ) j at hmem
  simp [Ne.symm hij] at hmem

lemma cell_pairwise_aedisjoint :
    Pairwise (fun i j : ι => AEDisjoint volume (cell i) (cell j)) := by
  intro i j hij
  exact measure_mono_null (cell_inter_cell_subset i j) (volume_coordinate_diagonal hij)

omit [DecidableEq ι] in
lemma cube_aedisjoint_cells :
    AEDisjoint volume (cube : Set (ι → ℝ)) (⋃ i, cell i) := by
  change volume (cube ∩ ⋃ i, cell i) = 0
  rw [inter_iUnion]
  exact measure_iUnion_null fun i =>
    measure_mono_null (cube_inter_cell_subset i) (volume_coordinate_hyperplane i 1)

/-- Lebesgue volume of the actual cube-plus-diagonal zonotope. -/
theorem volume_zonotope :
    volume (zonotope : Set (ι → ℝ)) = (Fintype.card ι : ℝ≥0∞) + 1 := by
  rw [zonotope_decomposition]
  rw [measure_union₀ (MeasurableSet.iUnion (fun i => (isCompact_cell i).measurableSet)).nullMeasurableSet
    cube_aedisjoint_cells]
  rw [volume_cube, measure_iUnion₀ cell_pairwise_aedisjoint
    (fun i => (isCompact_cell i).measurableSet.nullMeasurableSet)]
  simp [tsum_fintype, add_comm]

/-- Translation to the center does not change the computed volume. -/
theorem volume_centered :
    volume (centered : Set (ι → ℝ)) = (Fintype.card ι : ℝ≥0∞) + 1 := by
  change volume ((fun x : ι → ℝ => x + 1) ⁻¹' zonotope) = _
  rw [measure_preimage_add_right, volume_zonotope]

theorem volume_zonotope_fin (n : ℕ) :
    volume (zonotope : Set (Fin n → ℝ)) = (n : ℝ≥0∞) + 1 := by
  simpa using (volume_zonotope (ι := Fin n))

end DiagonalZonotope

end

end OAI
