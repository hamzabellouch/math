import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalTensorBound
import OAI.Analysis.Conductivity.Flux.PhysicalChildTensor
import OAI.Analysis.Conductivity.Geometry.PhysicalEndRegions

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance : MeasurableSpace (Matrix (Fin 3) (Fin 3) ℝ) := borel _
local instance : BorelSpace (Matrix (Fin 3) (Fin 3) ℝ) := ⟨rfl⟩

lemma childAxis_pi_norm (v : Fin 3 → ℝ) : ‖fun i => v (childAxis i)‖=‖v‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      (fun i => norm_le_pi_norm v (childAxis i))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (fun i => v (childAxis i)))).mpr
    intro i
    have h := norm_le_pi_norm (fun j => v (childAxis j)) (childAxis i)
    have he : childAxis (childAxis i)=i := by fin_cases i <;> rfl
    simpa only [he] using h

lemma sourceChildTensorPush_measurable (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) (hA : Measurable A) :
    Measurable (sourceChildTensorPush k A) := by
  let F : Matrix (Fin 3) (Fin 3) ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun M i j => sourceScale⁻¹*M (childAxis i) (childAxis j)
  have hc : Continuous F := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fun_prop
  have hm : Measurable F := hc.measurable
  exact hm.comp (hA.comp
    (sourceChildHomeomorph (actualChildSign k)).symm.continuous.measurable)

lemma sourceChildTensorPush_norm_bound (k : Fin 2)
    (A : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hA : ∀ y,‖A y‖ ≤ B) (y : Fin 3 → ℝ) :
    ‖sourceChildTensorPush k A y‖ ≤ |sourceScale⁻¹| * B := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) hB)).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (abs_nonneg _) hB)).mpr
  intro j
  change ‖sourceScale⁻¹*A _ (childAxis i) (childAxis j)‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact ((norm_le_pi_norm _ (childAxis j)).trans
    (norm_le_pi_norm _ (childAxis i))).trans (hA _)

def physicalEndTensor (s a : Fin 3 → ℝ) (i : Fin 3) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  Fin.cases (attachedCollarTensor s (a 0))
    (fun k => sourceChildTensorPush k (attachedCollarTensor s (a k.succ))) i

lemma physicalEndTensor_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (i : Fin 3) :
    Measurable (physicalEndTensor s a i) ∧
      (∀ y,(physicalEndTensor s a i y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalEndTensor s a i y*ᵥv) ∧
          v ⬝ᵥ (physicalEndTensor s a i y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖physicalEndTensor s a i y‖ ≤ B) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hp := attachedCollarTensor_properties s hs (ha 0)
    exact ⟨hp.1,hp.2.1,hp.2.2.1,attachedFaceTensorList_bounded s (ha 0) _⟩
  · have hp := attachedCollarTensor_properties s hs (ha k.succ)
    obtain ⟨c,C,hc,hcC,h⟩ := hp.2.2.1
    obtain ⟨B,hB,hbound⟩ := attachedFaceTensorList_bounded s (ha k.succ)
      (Finset.univ : Finset (Fin 4 × Fin 4)).toList
    have hspos : 0<sourceScale⁻¹ := by norm_num [sourceScale]
    refine ⟨sourceChildTensorPush_measurable k _ hp.1,
      sourceChildTensorPush_symmetric k _ hp.2.1,
      ⟨sourceScale⁻¹*c,sourceScale⁻¹*C,mul_pos hspos hc,
        mul_lt_mul_of_pos_left hcC hspos,?_⟩,
      ⟨|sourceScale⁻¹| * B,mul_pos (abs_pos.mpr hspos.ne') hB,
        sourceChildTensorPush_norm_bound k _ hB.le hbound⟩⟩
    intro y v
    change (sourceScale⁻¹*c)*‖v‖^2 ≤ v ⬝ᵥ (sourceChildTensorPush k _ y*ᵥv) ∧
      v ⬝ᵥ (sourceChildTensorPush k _ y*ᵥv) ≤ (sourceScale⁻¹*C)*‖v‖^2
    rw [sourceChildTensorPush_quadratic]
    have hh := h ((sourceChildHomeomorph (actualChildSign k)).symm y)
      (fun j => v (childAxis j))
    rw [childAxis_pi_norm] at hh
    exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hspos.le,
      by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hspos.le⟩

def physicalBlockTensorList (s a : Fin 3 → ℝ) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact is.foldr (fun i A => if y∈physicalEndRegion i then physicalEndTensor s a i y else A) 1

lemma physicalBlockTensorList_cons (s a : Fin 3 → ℝ) (i : Fin 3) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : physicalBlockTensorList s a (i::is) y=
      (by classical exact if y∈physicalEndRegion i then physicalEndTensor s a i y
        else physicalBlockTensorList s a is y) := rfl

lemma physicalBlockTensorList_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) (is : List (Fin 3)) :
    Measurable (physicalBlockTensorList s a is) ∧
      (∀ y,(physicalBlockTensorList s a is y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalBlockTensorList s a is y*ᵥv) ∧
          v ⬝ᵥ (physicalBlockTensorList s a is y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖physicalBlockTensorList s a is y‖ ≤ B) := by
  classical
  induction is with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨measurable_const,fun _ => Matrix.transpose_one,
      ⟨c,C,hc,hcC,fun _ => h⟩,
      ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
        change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ _; linarith⟩⟩
  | cons i is ih =>
    have hi := physicalEndTensor_properties s a hs ha i
    obtain ⟨c,C,hc,hcC,h⟩ := ih.2.2.1
    obtain ⟨d,D,hd,hdD,hlocal⟩ := hi.2.2.1
    obtain ⟨B,hB,hbound⟩ := ih.2.2.2
    obtain ⟨E,hE,hend⟩ := hi.2.2.2
    refine ⟨Measurable.ite (physicalEndRegion_compact i).measurableSet hi.1 ih.1,?_,
      ⟨min c d,max C D,lt_min hc hd,
        lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩,
      ⟨max B E,hB.trans_le (le_max_left _ _),?_⟩⟩
    · intro y
      rw [physicalBlockTensorList_cons]
      split_ifs
      · exact hi.2.1 y
      · exact ih.2.1 y
    · intro y v
      rw [physicalBlockTensorList_cons]
      split_ifs with hy
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hlocal y v).1,(hlocal y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,(h y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    · intro y
      rw [physicalBlockTensorList_cons]
      split_ifs
      · exact (hend y).trans (le_max_right _ _)
      · exact (hbound y).trans (le_max_left _ _)

def physicalBlockTensor (s a : Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  physicalBlockTensorList s a (Finset.univ : Finset (Fin 3)).toList

lemma physicalBlockTensor_local_list (s a : Fin 3 → ℝ) (is : List (Fin 3))
    (i : Fin 3) (hi : i∈is) {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    physicalBlockTensorList s a is y=physicalEndTensor s a i y := by
  classical
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    rw [physicalBlockTensorList_cons]
    by_cases he : j=i
    · subst j; simp only [ite_eq_left hy]
    · have hn : y∉physicalEndRegion j := fun hj =>
        (disjoint_left.mp (physicalEndRegion_pairwise_disjoint he) hj hy)
      rw [ite_eq_right hn]
      exact ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he))

lemma physicalBlockTensor_local (s a : Fin 3 → ℝ) (i : Fin 3)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    physicalBlockTensor s a y=physicalEndTensor s a i y :=
  physicalBlockTensor_local_list s a _ i (by simp) hy

lemma physicalBlockTensorList_outside (s a : Fin 3 → ℝ) (is : List (Fin 3))
    {y : Fin 3 → ℝ} (hy : ∀ i∈is,y∉physicalEndRegion i) :
    physicalBlockTensorList s a is y=1 := by
  classical
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [physicalBlockTensorList_cons,ite_eq_right (hy i List.mem_cons_self)]
    exact ih (fun j hj => hy j (List.mem_cons_of_mem i hj))

theorem physicalBlockTensor_properties (s a : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha : ∀ i,a i≠0) :
    Measurable (physicalBlockTensor s a) ∧
      MemLp (physicalBlockTensor s a) ∞ (volume : Measure (Fin 3 → ℝ)) ∧
      (∀ y,(physicalBlockTensor s a y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (physicalBlockTensor s a y*ᵥv) ∧
          v ⬝ᵥ (physicalBlockTensor s a y*ᵥv) ≤ C*‖v‖^2) ∧
      (∀ i y,y∈physicalEndRegion i → physicalBlockTensor s a y=physicalEndTensor s a i y) ∧
      (∀ y,(∀ i,y∉physicalEndRegion i) → physicalBlockTensor s a y=1) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  have h := physicalBlockTensorList_properties s a hs ha
    (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  exact ⟨h.1,memLp_top_of_bound h.1.aestronglyMeasurable B (ae_of_all _ hbound),
    h.2.1,h.2.2.1,fun i y hy => physicalBlockTensor_local s a i hy,
    fun y hy => physicalBlockTensorList_outside s a _ (fun i _ => hy i)⟩

end ScalarConductivity

end
end

end OAI
