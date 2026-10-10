import Mathlib

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CubeTiling_scope

open MeasureTheory Set
open scoped BigOperators unitInterval

variable {d : Type*} [Fintype d]

def floorCube (z : d → ℤ) : Set (d → ℝ) := {x | ∀ i, ⌊x i⌋ = z i}
def closedCube (z : d → ℤ) : Set (d → ℝ) := Set.univ.pi (fun i => Icc (z i:ℝ) ((z i:ℝ)+1))
def cubeShift (z : d → ℤ) (x : d → I) : d → ℝ := fun i => (z i:ℝ)+(x i:ℝ)

omit [Fintype d] in
lemma floorCube_pi (z : d → ℤ) :
    floorCube z = Set.univ.pi (fun i => Ico (z i:ℝ) ((z i:ℝ)+1)) := by
  ext x
  simp only [floorCube,Set.mem_ofPred_eq,Set.mem_univ_pi,Set.mem_Ico,Int.floor_eq_iff]

lemma floorCube_measurable (z : d → ℤ) : MeasurableSet (floorCube z) := by
  rw [floorCube_pi]
  exact MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

omit [Fintype d] in
lemma floorCube_disjoint : Pairwise (fun z w : d → ℤ => Disjoint (floorCube z) (floorCube w)) := by
  intro z w h
  rw [Set.disjoint_left]
  intro x hx hy
  apply h
  funext i
  exact (hx i).symm.trans (hy i)

omit [Fintype d] in
lemma floorCube_cover : ⋃ z : d → ℤ, floorCube z = Set.univ := by
  ext x
  simp only [Set.mem_iUnion,Set.mem_univ,iff_true]
  exact ⟨fun i => ⌊x i⌋,fun _ => rfl⟩

lemma floorCube_restrict (z : d → ℤ) :
    volume.restrict (floorCube z) = volume.restrict (closedCube z) := by
  rw [floorCube_pi,closedCube,volume_pi,Measure.restrict_pi_pi,Measure.restrict_pi_pi]
  congr 1
  funext i
  exact Measure.restrict_congr_set Ico_ae_eq_Icc

lemma cubeShift_preserving (z : d → ℤ) :
    MeasurePreserving (cubeShift z) volume (volume.restrict (closedCube z)) := by
  have hs (i : d) : MeasurePreserving (fun x : I => (z i:ℝ)+(x:ℝ))
      volume (volume.restrict (Icc (z i:ℝ) ((z i:ℝ)+1))) := by
    have ha := (measurePreserving_add_left (volume : Measure ℝ) (z i:ℝ)).restrict_preimage
      (measurableSet_Icc : MeasurableSet (Icc (z i:ℝ) ((z i:ℝ)+1)))
    have he : (fun x : ℝ => (z i:ℝ)+x) ⁻¹' Icc (z i:ℝ) ((z i:ℝ)+1) = Icc (0:ℝ) 1 := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
    rw [he] at ha
    exact ha.comp unitInterval.measurePreserving_coe
  have h := measurePreserving_pi (fun _ : d => (volume : Measure I))
    (fun i => volume.restrict (Icc (z i:ℝ) ((z i:ℝ)+1))) hs
  unfold cubeShift closedCube
  rw [volume_pi,volume_pi,Measure.restrict_pi_pi]
  exact h

lemma integral_cubeShift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : d → ℤ) (f : (d → ℝ) → E) (hf : AEStronglyMeasurable f (volume.restrict (closedCube z))) :
    (∫ x : d → I, f (cubeShift z x)) = ∫ x in floorCube z, f x := by
  rw [floorCube_restrict]
  have h := cubeShift_preserving z
  have hf' : AEStronglyMeasurable f (Measure.map (cubeShift z) volume) := by rwa [h.map_eq]
  simpa only [h.map_eq] using (integral_map h.measurable.aemeasurable hf').symm

lemma hasSum_integral_cubes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : (d → ℝ) → E} (hf : Integrable f) :
    HasSum (fun z : d → ℤ => ∫ x : d → I, f (cubeShift z x)) (∫ x, f x) := by
  have hh := hasSum_integral_iUnion floorCube_measurable floorCube_disjoint
    (f := f) (μ := volume) hf.integrableOn
  rw [floorCube_cover,Measure.restrict_univ] at hh
  simpa only [integral_cubeShift _ f hf.aestronglyMeasurable.restrict] using hh

end Work_CubeTiling_scope

open MeasureTheory Set Filter
open scoped BigOperators unitInterval Convolution

variable {d : Type*} [Fintype d]

def cubeChar (x : d → ℝ) : ℝ := (floorCube 0).indicator (fun _ => 1) x

def cubeOverlap (x : d → ℝ) : ℝ := ∫ t, cubeChar t*cubeChar (t-x)

lemma cubeChar_measurable : Measurable (cubeChar (d := d)) :=
  measurable_const.indicator (floorCube_measurable 0)

omit [Fintype d] in
lemma cubeChar_nonneg (x : d → ℝ) : 0 ≤ cubeChar x := by
  unfold cubeChar Set.indicator
  split_ifs <;> norm_num

omit [Fintype d] in
lemma cubeChar_le (x : d → ℝ) : cubeChar x ≤ 1 := by
  unfold cubeChar Set.indicator
  split_ifs <;> norm_num

lemma volume_floorCube (z : d → ℤ) : volume (floorCube z) = 1 := by
  rw [floorCube_pi,volume_pi,Measure.pi_pi]
  simp

lemma cubeChar_integrable : Integrable (cubeChar (d := d)) := by
  exact (integrableOn_const (C := (1:ℝ)) (by simp [volume_floorCube])).integrable_indicator (floorCube_measurable 0)

lemma integral_cubeChar : (∫ x : d → ℝ, cubeChar x) = 1 := by
  change (∫ x : d → ℝ, (floorCube 0).indicator (fun _ => (1:ℝ)) x) = 1
  rw [integral_indicator (floorCube_measurable 0),setIntegral_const]
  simp [measureReal_def,volume_floorCube]

lemma cubeOverlap_section_integrable (x : d → ℝ) :
    Integrable (fun t => cubeChar t*cubeChar (t-x)) := by
  rw [show (fun t => cubeChar t*cubeChar (t-x)) = fun t => cubeChar (t-x)*cubeChar t by funext; ring]
  apply cubeChar_integrable.bdd_mul (c := 1) (cubeChar_measurable.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
  exact Eventually.of_forall fun t => by
    change ‖cubeChar (t-x)‖ ≤ 1
    rw [Real.norm_of_nonneg (cubeChar_nonneg _)]; exact cubeChar_le _

lemma cubeOverlap_nonneg (x : d → ℝ) : 0 ≤ cubeOverlap x :=
  integral_nonneg (fun _ => mul_nonneg (cubeChar_nonneg _) (cubeChar_nonneg _))

lemma cubeOverlap_le (x : d → ℝ) : cubeOverlap x ≤ 1 := by
  rw [←integral_cubeChar (d := d)]
  exact integral_mono (cubeOverlap_section_integrable x) cubeChar_integrable
    (fun t => mul_le_of_le_one_right (cubeChar_nonneg _) (cubeChar_le _))

lemma cubeOverlap_measurable : Measurable (cubeOverlap (d := d)) := by
  have hm : Measurable (fun p : (d → ℝ) × (d → ℝ) => cubeChar p.1*cubeChar (p.1-p.2)) :=
    (cubeChar_measurable.comp measurable_fst).mul
      (cubeChar_measurable.comp (measurable_fst.sub measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

lemma cubeOverlap_convolution : cubeOverlap (d := d) =
    cubeChar ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] (fun x => cubeChar (-x)) := by
  funext x
  unfold cubeOverlap convolution
  congr 1
  funext t
  simp only [ContinuousLinearMap.mul_apply',neg_sub]

lemma cubeOverlap_integrable : Integrable (cubeOverlap (d := d)) := by
  rw [cubeOverlap_convolution]
  exact cubeChar_integrable.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    cubeChar_integrable.comp_neg

lemma integral_cubeOverlap : (∫ x : d → ℝ, cubeOverlap x) = 1 := by
  rw [cubeOverlap_convolution,integral_convolution _ cubeChar_integrable cubeChar_integrable.comp_neg]
  simp only [integral_neg_eq_self,ContinuousLinearMap.mul_apply',integral_cubeChar,one_mul]

omit [Fintype d] in
lemma cubeChar_eq_zero_of_not_mem {x : d → ℝ} (h : x ∉ floorCube 0) : cubeChar x = 0 :=
  indicator_of_notMem h _

omit [Fintype d] in
lemma cubeChar_pos_iff (x : d → ℝ) : 0 < cubeChar x ↔ x ∈ floorCube 0 := by
  unfold cubeChar
  by_cases h : x ∈ floorCube 0 <;> simp [h]

omit [Fintype d] in
lemma cubeChar_coord {x : d → ℝ} (h : x ∈ floorCube 0) (i : d) : 0 ≤ x i ∧ x i < 1 := by
  have hi := h i
  simpa only [Pi.zero_apply,Int.floor_eq_iff,Int.cast_zero,zero_add] using hi

lemma cubeOverlap_support_coord (x : d → ℝ) (i : d) (hx : 1 ≤ |x i|) : cubeOverlap x = 0 := by
  unfold cubeOverlap
  have he (t : d → ℝ) : cubeChar t*cubeChar (t-x) = 0 := by
    by_cases ht : t ∈ floorCube 0
    · by_cases hu : t-x ∈ floorCube 0
      · have h1 := cubeChar_coord ht i
        have h2 := cubeChar_coord hu i
        simp only [Pi.sub_apply] at h2
        rcases (le_abs.mp hx) with h | h <;> linarith
      · rw [cubeChar_eq_zero_of_not_mem hu,mul_zero]
    · rw [cubeChar_eq_zero_of_not_mem ht,zero_mul]
  simp only [he,integral_zero]

lemma lintegral_cube_periodization (f : (d → ℝ) → ENNReal) (hf : Measurable f) :
    (∫⁻ t : d → I, ∑' z : d → ℤ, f (cubeShift z t)) = ∫⁻ x, f x := by
  have hm (z : d → ℤ) : AEMeasurable (fun t : d → I => f (cubeShift z t)) :=
    (hf.comp (cubeShift_preserving z).measurable).aemeasurable
  rw [lintegral_tsum hm]
  have he (z : d → ℤ) : (∫⁻ t : d → I, f (cubeShift z t)) = ∫⁻ x in floorCube z, f x := by
    rw [floorCube_restrict]
    exact (cubeShift_preserving z).lintegral_comp hf
  simp only [he]
  rw [←lintegral_iUnion floorCube_measurable floorCube_disjoint, floorCube_cover,Measure.restrict_univ]

end CoulombNeumann

end

end OAI
