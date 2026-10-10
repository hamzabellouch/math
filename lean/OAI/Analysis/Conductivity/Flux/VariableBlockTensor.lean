import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalBlockTensor
import OAI.Analysis.Conductivity.Flux.VariableCollarTensor

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal
local instance variableBlockTensorMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance variableBlockTensorBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def variableEndTensor (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3) : Coord3 → Mat3 :=
  Fin.cases (variableCollarTensor (K 0) (a 0) centralThickness)
    (fun k => sourceChildTensorPush k
      (variableCollarTensor (K k.succ) (a k.succ) (-centralThickness))) i

lemma variableEndTensor_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (i : Fin 3) :
    Measurable (variableEndTensor K a i) ∧
      (∀ y,(variableEndTensor K a i y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Coord3),
        c*‖v‖^2≤v ⬝ᵥ(variableEndTensor K a i y*ᵥv) ∧
          v ⬝ᵥ(variableEndTensor K a i y*ᵥv)≤C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableEndTensor K a i y‖≤B) := by
  have hp (i : Fin 3) (b : ℝ) :
      Measurable (variableCollarTensor (K i) (a i) b) ∧
      (∀ y,(variableCollarTensor (K i) (a i) b y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Coord3),
        c*‖v‖^2≤v ⬝ᵥ(variableCollarTensor (K i) (a i) b y*ᵥv) ∧
          v ⬝ᵥ(variableCollarTensor (K i) (a i) b y*ᵥv)≤C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableCollarTensor (K i) (a i) b y‖≤B) := by
    obtain ⟨c,C,hc,hcC,hb⟩ := (hK i).2.2
    exact ⟨variableCollarTensor_measurable (hK i).1 _ _,variableCollarTensor_symm (hK i).2.1 _ _,
      variableCollarTensor_elliptic hc hcC hb (ha i) b,
      variableCollarTensor_bounded (hK i).2.1 hc hcC hb (ha i) b⟩
  refine Fin.cases (hp 0 centralThickness) (fun k => ?_) i
  have hk := hp k.succ (-centralThickness)
  obtain ⟨c,C,hc,hcC,h⟩ := hk.2.2.1
  obtain ⟨B,hB,hbound⟩ := hk.2.2.2
  have hspos : 0<sourceScale⁻¹ := by norm_num [sourceScale]
  have hmeas : Measurable (variableEndTensor K a k.succ) := by
    change Measurable (sourceChildTensorPush k _)
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact measurable_const.mul (((measurable_pi_apply _).comp
      ((measurable_pi_apply _).comp hk.1)).comp
      (sourceChildHomeomorph (actualChildSign k)).symm.continuous.measurable)
  refine ⟨hmeas,
    sourceChildTensorPush_symmetric k _ hk.2.1,
    ⟨sourceScale⁻¹*c,sourceScale⁻¹*C,mul_pos hspos hc,
      mul_lt_mul_of_pos_left hcC hspos,?_⟩,
    ⟨|sourceScale⁻¹| * B,mul_pos (abs_pos.mpr hspos.ne') hB,
      sourceChildTensorPush_norm_bound k _ hB.le hbound⟩⟩
  intro y v
  change (sourceScale⁻¹*c)*‖v‖^2≤v ⬝ᵥ(sourceChildTensorPush k _ y*ᵥv) ∧
    v ⬝ᵥ(sourceChildTensorPush k _ y*ᵥv)≤(sourceScale⁻¹*C)*‖v‖^2
  rw [sourceChildTensorPush_quadratic]
  have hh := h ((sourceChildHomeomorph (actualChildSign k)).symm y)
    (fun j => v (childAxis j))
  rw [childAxis_pi_norm] at hh
  exact ⟨by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.1 hspos.le,
    by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh.2 hspos.le⟩

def variableBlockTensorList (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := by
  classical
  exact is.foldr (fun i A => if y∈physicalEndRegion i then variableEndTensor K a i y else A) 1

lemma variableBlockTensorList_cons (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3) (is : List (Fin 3))
    (y : Fin 3 → ℝ) : variableBlockTensorList K a (i::is) y=
      (by classical exact if y∈physicalEndRegion i then variableEndTensor K a i y
        else variableBlockTensorList K a is y) := rfl

lemma variableBlockTensorList_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) (is : List (Fin 3)) :
    Measurable (variableBlockTensorList K a is) ∧
      (∀ y,(variableBlockTensorList K a is y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (variableBlockTensorList K a is y*ᵥv) ∧
          v ⬝ᵥ (variableBlockTensorList K a is y*ᵥv) ≤ C*‖v‖^2) ∧
      (∃ B : ℝ,0<B ∧ ∀ y,‖variableBlockTensorList K a is y‖ ≤ B) := by
  classical
  induction is with
  | nil =>
    obtain ⟨c,C,hc,hcC,h⟩ := identity_matrix_energy_bounds
    exact ⟨measurable_const,fun _ => Matrix.transpose_one,
      ⟨c,C,hc,hcC,fun _ => h⟩,
      ⟨‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖+1,by positivity,fun _ => by
        change ‖(1 : Matrix (Fin 3) (Fin 3) ℝ)‖ ≤ _; linarith⟩⟩
  | cons i is ih =>
    have hi := variableEndTensor_properties K a hK ha i
    obtain ⟨c,C,hc,hcC,h⟩ := ih.2.2.1
    obtain ⟨d,D,hd,hdD,hlocal⟩ := hi.2.2.1
    obtain ⟨B,hB,hbound⟩ := ih.2.2.2
    obtain ⟨E,hE,hend⟩ := hi.2.2.2
    refine ⟨Measurable.ite (physicalEndRegion_compact i).measurableSet hi.1 ih.1,?_,
      ⟨min c d,max C D,lt_min hc hd,
        lt_of_le_of_lt (min_le_left _ _) (hcC.trans_le (le_max_left _ _)),?_⟩,
      ⟨max B E,hB.trans_le (le_max_left _ _),?_⟩⟩
    · intro y
      rw [variableBlockTensorList_cons]
      split_ifs
      · exact hi.2.1 y
      · exact ih.2.1 y
    · intro y v
      rw [variableBlockTensorList_cons]
      split_ifs with hy
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)).trans
          (hlocal y v).1,(hlocal y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))⟩
      · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)).trans
          (h y v).1,(h y v).2.trans
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))⟩
    · intro y
      rw [variableBlockTensorList_cons]
      split_ifs
      · exact (hend y).trans (le_max_right _ _)
      · exact (hbound y).trans (le_max_left _ _)

def variableBlockTensor (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) :
    (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ :=
  variableBlockTensorList K a (Finset.univ : Finset (Fin 3)).toList

lemma variableBlockTensor_local_list (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    (i : Fin 3) (hi : i∈is) {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    variableBlockTensorList K a is y=variableEndTensor K a i y := by
  classical
  induction is with
  | nil => simp at hi
  | cons j is ih =>
    rw [variableBlockTensorList_cons]
    by_cases he : j=i
    · subst j; simp only [ite_eq_left hy]
    · have hn : y∉physicalEndRegion j := fun hj =>
        (disjoint_left.mp (physicalEndRegion_pairwise_disjoint he) hj hy)
      rw [ite_eq_right hn]
      exact ih ((List.mem_cons.mp hi).resolve_left (Ne.symm he))

lemma variableBlockTensor_local (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (i : Fin 3)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    variableBlockTensor K a y=variableEndTensor K a i y :=
  variableBlockTensor_local_list K a _ i (by simp) hy

lemma variableBlockTensorList_outside (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ) (is : List (Fin 3))
    {y : Fin 3 → ℝ} (hy : ∀ i∈is,y∉physicalEndRegion i) :
    variableBlockTensorList K a is y=1 := by
  classical
  induction is with
  | nil => rfl
  | cons i is ih =>
    rw [variableBlockTensorList_cons,ite_eq_right (hy i List.mem_cons_self)]
    exact ih (fun j hj => hy j (List.mem_cons_of_mem i hj))

theorem variableBlockTensor_properties (K : Fin 3 → Coord3 → Mat3) (a : Fin 3 → ℝ)
    (hK : ∀ i,Measurable (K i) ∧ (∀ x,(K i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(K i x*ᵥv) ∧ v ⬝ᵥ(K i x*ᵥv)≤C*(v ⬝ᵥ v))
    (ha : ∀ i,a i≠0) :
    Measurable (variableBlockTensor K a) ∧
      MemLp (variableBlockTensor K a) ∞ (volume : Measure (Fin 3 → ℝ)) ∧
      (∀ y,(variableBlockTensor K a y).IsSymm) ∧
      (∃ c C : ℝ,0<c ∧ c<C ∧ ∀ y (v : Fin 3 → ℝ),
        c*‖v‖^2 ≤ v ⬝ᵥ (variableBlockTensor K a y*ᵥv) ∧
          v ⬝ᵥ (variableBlockTensor K a y*ᵥv) ≤ C*‖v‖^2) ∧
      (∀ i y,y∈physicalEndRegion i → variableBlockTensor K a y=variableEndTensor K a i y) ∧
      (∀ y,(∀ i,y∉physicalEndRegion i) → variableBlockTensor K a y=1) := by
  let : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 3 → Fin 3 → ℝ))
  let : SecondCountableTopology (Matrix (Fin 3) (Fin 3) ℝ) :=
    inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → ℝ))
  have h := variableBlockTensorList_properties K a hK ha
    (Finset.univ : Finset (Fin 3)).toList
  obtain ⟨B,hB,hbound⟩ := h.2.2.2
  exact ⟨h.1,memLp_top_of_bound h.1.aestronglyMeasurable B (ae_of_all _ hbound),
    h.2.1,h.2.2.1,fun i y hy => variableBlockTensor_local K a i hy,
    fun y hy => variableBlockTensorList_outside K a _ (fun i _ => hy i)⟩

end ScalarConductivity

end
end

end OAI
