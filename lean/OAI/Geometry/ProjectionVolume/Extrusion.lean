import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Convex.Segment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

universe uι

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Paper092

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def unitCube (ι : Type uι) : Set (ι → ℝ) := Icc 0 1

def extrusionCell (i : ι) : Set (ι → ℝ) :=
  {x | (1 ≤ x i ∧ x i ≤ 2) ∧ ∀ j, j ≠ i → x i - 1 ≤ x j ∧ x j ≤ x i}

def shearMatrix (i : ι) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ).updateCol i (fun _ => 1)

theorem det_shearMatrix (i : ι) : (shearMatrix i).det = 1 := by
  simpa [shearMatrix, Matrix.one_apply] using
    Matrix.det_updateCol_sum (1 : Matrix ι ι ℝ) i (fun _ => (1 : ℝ))

def cellMap (i : ι) (x : ι → ℝ) : ι → ℝ :=
  fun j => if j = i then 1 + x i else x i + x j

omit [Fintype ι] in
theorem cellMap_mem_iff (i : ι) (x : ι → ℝ) :
    cellMap i x ∈ extrusionCell i ↔ x ∈ unitCube ι := by
  simp only [extrusionCell, cellMap, unitCube, mem_ofPred_eq, mem_Icc, Pi.le_def,
    Pi.zero_apply, Pi.one_apply, ite_true]
  constructor
  · rintro ⟨hi, h⟩
    constructor <;> intro j
    · by_cases hj : j = i
      · subst j; linarith
      · have := h j hj
        simp only [ite_eq_right hj] at this
        linarith
    · by_cases hj : j = i
      · subst j; linarith
      · have := h j hj
        simp only [ite_eq_right hj] at this
        linarith
  · rintro ⟨h0, h1⟩
    refine ⟨⟨by linarith [h0 i], by linarith [h1 i]⟩, ?_⟩
    intro j hj
    simp only [ite_eq_right hj]
    constructor <;> linarith [h0 j, h1 j]

theorem cellMap_eq_matrix (i : ι) (x : ι → ℝ) :
    cellMap i x = Pi.single i 1 + Matrix.toLin' (shearMatrix i) x := by
  funext j
  simp only [cellMap, Pi.add_apply, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    shearMatrix, Matrix.updateCol_apply, Matrix.one_apply]
  by_cases hj : j = i
  · subst j
    have hsum : ∀ k : ι,
        (if k = i then 1 else if i = k then 1 else 0) * x k =
          if k = i then x k else 0 := by
      intro k
      by_cases hk : k = i
      · subst k; simp
      · simp [hk, Ne.symm hk]
    simp_rw [hsum]
    simp
  · have hsum : ∀ k : ι,
        (if k = i then 1 else if j = k then 1 else 0) * x k =
          (if k = i then x i else 0) + (if k = j then x j else 0) := by
      intro k
      by_cases hki : k = i
      · subst k; simp [Ne.symm hj]
      · by_cases hkj : k = j
        · subst k; simp [hj]
        · simp [hki, hkj, Ne.symm hkj]
    simp_rw [hsum]
    simp [hj, Finset.sum_add_distrib]

theorem cellMap_measurePreserving (i : ι) :
    MeasurePreserving (cellMap i) volume volume := by
  have hs : MeasurePreserving (Matrix.toLin' (shearMatrix i)) volume volume := by
    refine ⟨(Matrix.toLin' (shearMatrix i)).continuous_of_finiteDimensional.measurable, ?_⟩
    simpa [det_shearMatrix] using
      Real.map_matrix_volume_pi_eq_smul_volume_pi
        (M := shearMatrix i) (by rw [det_shearMatrix]; norm_num)
  have h := (measurePreserving_add_left (volume : Measure (ι → ℝ)) (Pi.single i 1)).comp hs
  simpa only [Function.comp_def, ← cellMap_eq_matrix] using h

omit [DecidableEq ι] in
theorem extrusionCell_measurable (i : ι) : MeasurableSet (extrusionCell i) := by
  simp only [extrusionCell, ofPred_and, ofPred_forall]
  exact ((measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (measurable_pi_apply i) measurable_const)).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_le ((measurable_pi_apply i).sub measurable_const)
        (measurable_pi_apply j)).inter
      (measurableSet_le (measurable_pi_apply j) (measurable_pi_apply i)))

omit [DecidableEq ι] in
theorem unitCube_volume : volume (unitCube ι) = 1 := by
  simp [unitCube, Real.volume_Icc_pi]

theorem extrusionCell_volume (i : ι) : volume (extrusionCell i) = 1 := by
  have hpre : cellMap i ⁻¹' extrusionCell i = unitCube ι :=
    Set.ext (cellMap_mem_iff i)
  rw [← (cellMap_measurePreserving i).measure_preimage
    (extrusionCell_measurable i).nullMeasurableSet, hpre, unitCube_volume]

omit [DecidableEq ι] in
theorem coordinate_eq_null (i : ι) (c : ℝ) :
    volume {x : ι → ℝ | x i = c} = 0 := by
  simpa [volume_pi] using Measure.pi_hyperplane (fun _ : ι => (volume : Measure ℝ)) i c

theorem coordinates_eq_null (i j : ι) (hij : i ≠ j) :
    volume {x : ι → ℝ | x i = x j} = 0 := by
  let f : (ι → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ) - LinearMap.proj j
  have hker : LinearMap.ker f ≠ ⊤ := by
    intro h
    have hz : f (Pi.single i 1) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [h]
      exact Submodule.mem_top
    simp [f, Ne.symm hij] at hz
  have hset : {x : ι → ℝ | x i = x j} = (LinearMap.ker f : Set (ι → ℝ)) := by
    ext x
    change x i = x j ↔ x i - x j = 0
    exact sub_eq_zero.symm
  rw [hset]
  exact Measure.addHaar_submodule (volume : Measure (ι → ℝ)) (LinearMap.ker f) hker

omit [DecidableEq ι] in
theorem cube_cell_aedisjoint (i : ι) :
    AEDisjoint volume (unitCube ι) (extrusionCell i) := by
  apply measure_mono_null _ (coordinate_eq_null i 1)
  rintro x ⟨hx, hi⟩
  exact le_antisymm (hx.2 i) hi.1.1

theorem cells_aedisjoint : Pairwise (fun i j : ι =>
    AEDisjoint volume (extrusionCell i) (extrusionCell j)) := by
  intro i j hij
  apply measure_mono_null _ (coordinates_eq_null i j hij)
  rintro x ⟨hi, hj⟩
  exact le_antisymm (hj.2 i hij).2 (hi.2 j hij.symm).2

theorem cube_add_diagonal_eq_union [Nonempty ι] :
    unitCube ι + segment ℝ (0 : ι → ℝ) 1 =
      unitCube ι ∪ ⋃ i, extrusionCell i := by
  ext x
  constructor
  · rintro ⟨q, hq, z, hz, rfl⟩
    change (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) at hq
    rw [segment_eq_image] at hz
    rcases hz with ⟨t, ht, rfl⟩
    simp only [smul_zero, zero_add]
    by_cases hmax : ∀ i, q i + t ≤ 1
    · left
      constructor <;> intro i
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
        exact add_nonneg (hq.1 i) ht.1
      · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          using hmax i
    · right
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ q Finset.univ_nonempty
      refine mem_iUnion.mpr ⟨i, ?_⟩
      push Not at hmax
      obtain ⟨j, hj⟩ := hmax
      have hji := hi j (Finset.mem_univ j)
      constructor
      · constructor
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          linarith
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
          linarith [hq.2 i, ht.2]
      · intro k _
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one]
        constructor
        · linarith [hq.2 i, hq.1 k]
        · linarith [hi k (Finset.mem_univ k)]
  · rintro (hx | hx)
    · exact ⟨x, hx, 0, left_mem_segment ℝ _ _, add_zero x⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      refine ⟨fun j => x j - (x i - 1), ?_, (x i - 1) • (1 : ι → ℝ), ?_, ?_⟩
      · constructor <;> intro j
        · change 0 ≤ x j - (x i - 1)
          by_cases hj : j = i
          · subst j; linarith
          · linarith [(hi.2 j hj).1]
        · change x j - (x i - 1) ≤ 1
          by_cases hj : j = i
          · subst j; linarith
          · linarith [(hi.2 j hj).2]
      · rw [segment_eq_image]
        refine ⟨x i - 1, ⟨by linarith [hi.1.1], by linarith [hi.1.2]⟩, ?_⟩
        simp
      · ext j
        simp

theorem volume_cube_add_diagonal [Nonempty ι] :
    volume (unitCube ι + segment ℝ (0 : ι → ℝ) 1) = Fintype.card ι + 1 := by
  rw [cube_add_diagonal_eq_union,
    measure_union₀ ((MeasurableSet.iUnion extrusionCell_measurable).nullMeasurableSet)
      (AEDisjoint.iUnion_right_iff.mpr cube_cell_aedisjoint),
    measure_iUnion₀ cells_aedisjoint (fun i => (extrusionCell_measurable i).nullMeasurableSet),
    unitCube_volume]
  simp [extrusionCell_volume, add_comm]

theorem volume_Icc_add_segment_one (d : ℕ) (hd : 0 < d) :
    volume (Icc (0 : Fin d → ℝ) 1 + segment ℝ (0 : Fin d → ℝ) 1) = d + 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  simpa [unitCube] using (volume_cube_add_diagonal (ι := Fin d))

end Paper092

end OAI
