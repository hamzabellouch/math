import OAI.Geometry.CylinderCovering.Angular.GeometryDefinitions
import OAI.Geometry.RuledCovering.Main

namespace OAI

open Set MeasureTheory
open RuledApproximation
noncomputable section
namespace AngularGeometry

def lowerCylinder (h τ α β : ℝ) (P : Set Plane) : Cylinder :=
  projectedCylinder h (vec2 (τ * α) (τ * β)) P

def upperCylinder (h τ α β : ℝ) (P : Set Plane) : Cylinder :=
  ((lowerCylinder h τ (-α) (-β) P).rotate swapReflect).translate (vec3 0 0 h)

lemma lowerCylinder_axis (h τ α β : ℝ) (P : Set Plane) :
    (lowerCylinder h τ α β P).axis =
      ‖vec3 1 (τ * α) (h * (τ * β))‖⁻¹ • vec3 1 (τ * α) (h * (τ * β)) := rfl

lemma upperCylinder_axis (h τ α β : ℝ) (P : Set Plane) :
    (upperCylinder h τ α β P).axis =
      ‖vec3 (-τ * α) 1 (h * (τ * β))‖⁻¹ • vec3 (-τ * α) 1 (h * (τ * β)) := by
  have hdir : swapReflect (physicalDirection h (vec2 (τ * -α) (τ * -β))) =
      vec3 (-τ * α) 1 (h * (τ * β)) := by
    ext i
    fin_cases i <;> simp [swapReflect, physicalDirection, vec2, vec3]
  have hn : ‖physicalDirection h (vec2 (τ * -α) (τ * -β))‖ =
      ‖vec3 (-τ * α) 1 (h * (τ * β))‖ := by
    rw [← hdir, swapReflect.norm_map]
  change swapReflect (‖physicalDirection h (vec2 (τ * -α) (τ * -β))‖⁻¹ •
    physicalDirection h (vec2 (τ * -α) (τ * -β))) = _
  rw [map_smul, hdir, hn]

lemma lowerCylinder_carrier (h τ α β : ℝ) (P : Set Plane) :
    (lowerCylinder h τ α β P).carrier = lowerCarrier h τ α β P := by
  ext z
  rw [lowerCylinder, projectedCylinder_mem_iff]
  constructor
  · rintro ⟨p, hp, x, rfl⟩
    refine ⟨p, hp, x, ?_⟩
    ext i
    fin_cases i <;> simp [planeEmbedding, physicalDirection, vec2, vec3] <;> ring
  · rintro ⟨p, hp, x, rfl⟩
    refine ⟨p, hp, x, ?_⟩
    ext i
    fin_cases i <;> simp [planeEmbedding, physicalDirection, vec2, vec3] <;> ring

lemma upperCylinder_carrier (h τ α β : ℝ) (P : Set Plane) :
    (upperCylinder h τ α β P).carrier = upperCarrier h τ α β P := by
  rw [upperCylinder, Cylinder.translate_carrier, Cylinder.rotate_carrier,
    lowerCylinder_carrier]
  ext z
  constructor
  · rintro ⟨_, ⟨_, ⟨p, hp, y, rfl⟩, rfl⟩, rfl⟩
    refine ⟨p, hp, y, ?_⟩
    ext i
    fin_cases i <;> simp [swapReflect, vec3] <;> ring
  · rintro ⟨p, hp, y, rfl⟩
    refine ⟨_, ⟨_, ⟨p, hp, y, rfl⟩, rfl⟩, ?_⟩
    ext i
    fin_cases i <;> simp [swapReflect, vec3] <;> ring

lemma lowerCylinder_area {h : ℝ} (hh : 0 < h) (τ α β : ℝ) (P : Set Plane) :
    (lowerCylinder h τ α β P).area = areaFactor h τ α β * volume.real P := by
  rw [lowerCylinder, projectedCylinder_area hh]
  unfold physicalWeight areaFactor
  simp only [vec2_apply_zero, vec2_apply_one]
  have heq : 1 + (τ * α) ^ 2 + h ^ 2 * (τ * β) ^ 2 =
      1 + τ ^ 2 * (α ^ 2 + h ^ 2 * β ^ 2) := by ring
  rw [heq]
  ring

lemma upperCylinder_area {h : ℝ} (hh : 0 < h) (τ α β : ℝ) (P : Set Plane) :
    (upperCylinder h τ α β P).area = areaFactor h τ α β * volume.real P := by
  rw [upperCylinder, Cylinder.translate_area, Cylinder.rotate_area, lowerCylinder_area hh]
  simp [areaFactor]

lemma lowerCylinder_compact (h τ α β : ℝ) {P : Set Plane} (hP : IsCompact P) :
    IsCompact (lowerCylinder h τ α β P).base := by
  exact hP.image (perpendicularProjection h (vec2 (τ * α) (τ * β))).continuous_of_finiteDimensional

lemma upperCylinder_compact (h τ α β : ℝ) {P : Set Plane} (hP : IsCompact P) :
    IsCompact (upperCylinder h τ α β P).base := by
  apply IsCompact.image _ (by fun_prop)
  apply IsCompact.image _ (rotatedPlane _ swapReflect).continuous
  exact lowerCylinder_compact h τ (-α) (-β) hP

lemma lowerCylinder_measurable_finite (h τ α β : ℝ) {P : Set Plane} (hP : IsCompact P) :
    MeasurableSet (lowerCylinder h τ α β P).base ∧
      volume (lowerCylinder h τ α β P).base ≠ ⊤ := by
  have hc := lowerCylinder_compact h τ α β hP
  exact ⟨hc.measurableSet, hc.measure_lt_top.ne⟩

lemma upperCylinder_measurable_finite (h τ α β : ℝ) {P : Set Plane} (hP : IsCompact P) :
    MeasurableSet (upperCylinder h τ α β P).base ∧
      volume (upperCylinder h τ α β P).base ≠ ⊤ := by
  have hc := upperCylinder_compact h τ α β hP
  exact ⟨hc.measurableSet, hc.measure_lt_top.ne⟩

lemma pair_families {N : ℕ} (shape : Cylinder → Prop) (L U : Fin N → Cylinder)
    (hL : ∀ j, shape (L j)) (hU : ∀ j, shape (U j)) :
    ∃ C : Fin (2 * N) → Cylinder, (∀ i, shape (C i)) ∧
      familySet C = familySet L ∪ familySet U ∧
      familyArea C = familyArea L + familyArea U := by
  rw [Nat.two_mul]
  refine ⟨Fin.addCases L U, ?_, ?_, ?_⟩
  · intro i
    exact Fin.addCases (fun j => by simpa only [Fin.addCases_left] using hL j)
      (fun j => by simpa only [Fin.addCases_right] using hU j) i
  · ext z
    simp only [familySet, mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i hi
      · intro hj
        exact Or.inl ⟨j, by simpa only [Fin.addCases_left] using hj⟩
      · intro hj
        exact Or.inr ⟨j, by simpa only [Fin.addCases_right] using hj⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · exact ⟨j.castAdd N, by simpa only [Fin.addCases_left] using hj⟩
      · exact ⟨j.natAdd N, by simpa only [Fin.addCases_right] using hj⟩
  · simp only [familyArea, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right]

theorem paired_family {N : ℕ} {h : ℝ} (hh : 0 < h) (τ : ℝ)
    (α β : Fin N → ℝ) (P : Fin N → Set Plane) (hP : ∀ j, IsCompact (P j)) :
    ∃ C : Fin (2 * N) → Cylinder,
      (∀ i, IsCompact (C i).base ∧ MeasurableSet (C i).base ∧ volume (C i).base ≠ ⊤) ∧
      familySet C = (⋃ j, lowerCarrier h τ (α j) (β j) (P j)) ∪
        (⋃ j, upperCarrier h τ (α j) (β j) (P j)) ∧
      familyArea C = 2 * ∑ j, areaFactor h τ (α j) (β j) * volume.real (P j) := by
  obtain ⟨C, hC, hset, harea⟩ := pair_families
    (fun c => IsCompact c.base ∧ MeasurableSet c.base ∧ volume c.base ≠ ⊤)
    (fun j => lowerCylinder h τ (α j) (β j) (P j))
    (fun j => upperCylinder h τ (α j) (β j) (P j))
    (fun j => ⟨lowerCylinder_compact h τ (α j) (β j) (hP j),
      lowerCylinder_measurable_finite h τ (α j) (β j) (hP j)⟩)
    (fun j => ⟨upperCylinder_compact h τ (α j) (β j) (hP j),
      upperCylinder_measurable_finite h τ (α j) (β j) (hP j)⟩)
  refine ⟨C, hC, ?_, ?_⟩
  · simpa only [familySet, lowerCylinder_carrier, upperCylinder_carrier] using hset
  · rw [harea]
    simp only [familyArea, lowerCylinder_area hh, upperCylinder_area hh]
    ring

lemma areaFactor_sqrt_two (τ α β : ℝ) :
    areaFactor (Real.sqrt 2) τ α β =
      Real.sqrt 2 / Real.sqrt (1 + τ ^ 2 * (α ^ 2 + 2 * β ^ 2)) := by
  unfold areaFactor
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem paired_cover {N : ℕ} {h : ℝ} (hh : 0 < h) (τ : ℝ)
    (α β : Fin N → ℝ) (P : Fin N → Set Plane) (hP : ∀ j, IsCompact (P j))
    (S : Set Space) (hcov : S ⊆ (⋃ j, lowerCarrier h τ (α j) (β j) (P j)) ∪
      (⋃ j, upperCarrier h τ (α j) (β j) (P j))) :
    ∃ C : Fin (2 * N) → Cylinder,
      (∀ i, IsCompact (C i).base ∧ MeasurableSet (C i).base ∧ volume (C i).base ≠ ⊤) ∧
      S ⊆ familySet C ∧
      familyArea C = 2 * ∑ j, areaFactor h τ (α j) (β j) * volume.real (P j) := by
  obtain ⟨C, hC, hset, harea⟩ := paired_family hh τ α β P hP
  exact ⟨C, hC, hset.symm ▸ hcov, harea⟩

end AngularGeometry

end

end OAI
