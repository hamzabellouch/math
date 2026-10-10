import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonArea
open Classical Set MeasureTheory

local instance : Countable CutRing :=
  (QuadraticAlgebra.equivProd (1 : ℤ) 1).injective.countable

theorem continuous_cutForm (a : ℕ) (j : Fin 4) : Continuous (cutForm a j) := by
  change Continuous (fun p => cutForm a j p)
  fin_cases j <;> dsimp [cutForm] <;> fun_prop

theorem measurableSet_avoidsCuts (a : ℕ) : MeasurableSet {p : ℝ×ℝ | AvoidsCuts a p} := by
  change MeasurableSet {p | ∀j z,cutForm a j p≠ordinary z}
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro z
  exact ((continuous_cutForm a j).measurable (measurableSet_singleton (ordinary z))).compl

theorem volume_cut_level (a : ℕ) (j : Fin 4) (r : ℝ) :
    volume {p : ℝ×ℝ | cutForm a j p=r}=0 := by
  have hm : MeasurableSet {p : ℝ×ℝ | cutForm a j p=r} :=
    (continuous_cutForm a j).measurable (measurableSet_singleton r)
  change ((volume : Measure ℝ).prod volume) _=0
  fin_cases j
  · rw [Measure.prod_apply_symm hm]
    simp [cutForm]
  · rw [Measure.prod_apply hm]
    simp [cutForm]
  · rw [Measure.prod_apply hm]
    have hy (x : ℝ) : {y : ℝ | y-Real.goldenRatio^a*x=r}={r+Real.goldenRatio^a*x} := by
      ext y
      simp only [mem_ofPred_eq,mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [cutForm,Set.preimage]
    simp [hy]
  · rw [Measure.prod_apply_symm hm]
    have hx (y : ℝ) : {x : ℝ | x-Real.goldenRatio^a*y=r}={r+Real.goldenRatio^a*y} := by
      ext x
      simp only [mem_ofPred_eq,mem_singleton_iff]
      constructor <;> intro h <;> linarith
    simp only [cutForm,Set.preimage]
    simp [hx]

theorem ae_avoidsCuts (a : ℕ) : ∀ᵐp : ℝ×ℝ, AvoidsCuts a p := by
  rw [ae_iff]
  have he : {p : ℝ×ℝ | ¬AvoidsCuts a p}=⋃j : Fin 4,⋃z : CutRing,{p | cutForm a j p=ordinary z} := by
    ext p
    simp [AvoidsCuts]
  rw [he]
  exact measure_iUnion_null (fun j => measure_iUnion_null (fun z => volume_cut_level a j (ordinary z)))

theorem measurableSet_genericSquare (a : ℕ) :
    MeasurableSet {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p} :=
  (measurable_fst measurableSet_Ico).inter
    ((measurable_snd measurableSet_Ico).inter (measurableSet_avoidsCuts a))

theorem volume_genericSquare (a : ℕ) :
    volume {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p}=1 := by
  have he : {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p}
      =ᵐ[volume] (Ico (0:ℝ) 1)×ˢ(Ico (0:ℝ) 1) := by
    filter_upwards [ae_avoidsCuts a] with p hp
    apply propext
    change (p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p) ↔
      (p.1∈Ico 0 1 ∧ p.2∈Ico 0 1)
    simp only [hp,and_true]
  rw [measure_congr he]
  change ((volume : Measure ℝ).prod volume) (Ico 0 1 ×ˢ Ico 0 1)=1
  rw [Measure.prod_prod]
  simp

end PolygonArea

section PolygonJordan
open Classical Set MeasureTheory
namespace PolygonArea

noncomputable def square : Set (ℝ×ℝ) := Ico (0:ℝ) 1 ×ˢ Ico (0:ℝ) 1

theorem null_frontier_inter {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S∩T))=0 := by
  apply measure_mono_null (subset_trans (frontier_inter_subset S T) ?_)
    (measure_union_null hS hT)
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

theorem null_frontier_union {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S∪T))=0 := by
  apply measure_mono_null (subset_trans (frontier_union_subset S T) ?_)
    (measure_union_null hS hT)
  exact Set.union_subset_union Set.inter_subset_left Set.inter_subset_right

theorem null_frontier_diff {S T : Set (ℝ×ℝ)}
    (hS : volume (frontier S)=0) (hT : volume (frontier T)=0) :
    volume (frontier (S\T))=0 := by
  change volume (frontier (S ∩ Tᶜ))=0
  exact null_frontier_inter hS (by simpa only [frontier_compl] using hT)

theorem null_frontier_cut (a : ℕ) (j : Fin 4) (r : ℝ) :
    volume (frontier {p : ℝ×ℝ | cutForm a j p<r})=0 := by
  have h := (continuous_cutForm a j).frontier_preimage_subset (Iio r)
  rw [frontier_Iio] at h
  exact measure_mono_null h (volume_cut_level a j r)

theorem null_frontier_square : volume (frontier square)=0 := by
  have hcoord (j : Fin 4) : volume (frontier (cutForm 0 j ⁻¹' Ico (0:ℝ) 1))=0 := by
    apply measure_mono_null ((continuous_cutForm 0 j).frontier_preimage_subset _)
    rw [frontier_Ico (by norm_num : (0:ℝ)<1)]
    have he : cutForm 0 j ⁻¹' ({0,1} : Set ℝ)=
        {p | cutForm 0 j p=0}∪{p | cutForm 0 j p=1} := by ext p; simp
    rw [he]
    exact measure_union_null (volume_cut_level 0 j 0) (volume_cut_level 0 j 1)
  exact null_frontier_inter (hcoord 0) (hcoord 1)

theorem representative {a : ℕ} {U : Set (GenericSquare a)} (hU : U∈polygonAlgebra a) :
    ∃S : Set (ℝ×ℝ), S⊆square ∧ MeasurableSet S ∧ volume (frontier S)=0 ∧
      ∀x : GenericSquare a,x∈U ↔ x.val∈S := by
  apply polygon_induction (P:=fun U => ∃S : Set (ℝ×ℝ), S⊆square ∧ MeasurableSet S ∧
    volume (frontier S)=0 ∧ ∀x : GenericSquare a,x∈U ↔ x.val∈S) ?_ ?_ ?_ ?_ hU
  · intro j z
    refine ⟨square∩{p | cutForm a j p<ordinary z},Set.inter_subset_left,?_,
      null_frontier_inter null_frontier_square (null_frontier_cut a j (ordinary z)),?_⟩
    · exact (measurableSet_Ico.prod measurableSet_Ico).inter
        (isOpen_lt (continuous_cutForm a j) continuous_const).measurableSet
    · intro x
      change cutForm a j x.val<ordinary z ↔ x.val∈square ∧ cutForm a j x.val<ordinary z
      exact ⟨fun hx => ⟨⟨x.property.1,x.property.2.1⟩,hx⟩,And.right⟩
  · exact ⟨∅,Set.empty_subset _,MeasurableSet.empty,by simp,by simp⟩
  · intro U V hU hV
    obtain ⟨S,hS,hmS,hbS,heS⟩ := hU
    obtain ⟨T,hT,hmT,hbT,heT⟩ := hV
    exact ⟨S∪T,Set.union_subset hS hT,hmS.union hmT,null_frontier_union hbS hbT,
      fun x => or_congr (heS x) (heT x)⟩
  · intro U hU
    obtain ⟨S,hS,hmS,hbS,heS⟩ := hU
    refine ⟨square\S,Set.sdiff_subset,(measurableSet_Ico.prod measurableSet_Ico).diff hmS,
      null_frontier_diff null_frontier_square hbS,?_⟩
    intro x
    change x∉U ↔ x.val∈square ∧ x.val∉S
    exact ⟨fun hx => ⟨⟨x.property.1,x.property.2.1⟩,fun hs => hx ((heS x).mpr hs)⟩,
      fun hx hu => hx.2 ((heS x).mp hu)⟩

noncomputable def area {a : ℕ} (U : polygonAlgebra a) : ENNReal :=
  volume (Subtype.val '' U.val)

theorem image_eq_rep {a : ℕ} (U : polygonAlgebra a) {S : Set (ℝ×ℝ)}
    (hS : S⊆square) (he : ∀x : GenericSquare a,x∈U.val ↔ x.val∈S) :
    Subtype.val '' U.val=S∩{p | AvoidsCuts a p} := by
  ext p
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨(he x).mp hx,x.property.2.2⟩
  · rintro ⟨hp,hcut⟩
    have hsq := hS hp
    exact ⟨⟨p,hsq.1,hsq.2,hcut⟩,(he _).mpr hp,rfl⟩

theorem area_eq_rep {a : ℕ} (U : polygonAlgebra a) {S : Set (ℝ×ℝ)}
    (hS : S⊆square) (he : ∀x : GenericSquare a,x∈U.val ↔ x.val∈S) : area U=volume S := by
  rw [area,image_eq_rep U hS he]
  apply measure_congr
  filter_upwards [ae_avoidsCuts a] with p hp
  apply propext
  exact ⟨And.left,fun h => ⟨h,hp⟩⟩

theorem measurable_image {a : ℕ} (U : polygonAlgebra a) :
    MeasurableSet (Subtype.val '' U.val) := by
  obtain ⟨S,hS,hm,hn,he⟩ := representative U.property
  rw [image_eq_rep U hS he]
  exact hm.inter (measurableSet_avoidsCuts a)

theorem area_le_one {a : ℕ} (U : polygonAlgebra a) : area U≤1 := by
  obtain ⟨S,hS,hm,hn,he⟩ := representative U.property
  rw [area_eq_rep U hS he]
  calc
    volume S≤volume square := measure_mono hS
    _=1 := by change ((volume : Measure ℝ).prod volume) (Ico 0 1 ×ˢ Ico 0 1)=1; simp

theorem area_top (a : ℕ) : area (⊤ : polygonAlgebra a)=1 := by
  change volume (Subtype.val '' (⊤ : polygonAlgebra a).val)=1
  have he : Subtype.val '' (⊤ : polygonAlgebra a).val=
      {p : ℝ×ℝ | p.1∈Ico 0 1 ∧ p.2∈Ico 0 1 ∧ AvoidsCuts a p} := by
    ext p
    constructor
    · rintro ⟨x,-,rfl⟩; exact x.property
    · intro h; exact ⟨⟨p,h⟩,by trivial,rfl⟩
  rw [he]
  exact volume_genericSquare a

theorem closure_ae_eq {S : Set (ℝ×ℝ)} (hS : volume (frontier S)=0) : closure S=ᵐ[volume] S := by
  have hn : ∀ᵐp : ℝ×ℝ,p∉frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hS
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro hx
    exact interior_subset (show p∈interior S from by
      by_contra hn
      exact hp ⟨hx,hn⟩)
  · intro hx
    exact subset_closure hx

theorem interior_ae_eq {S : Set (ℝ×ℝ)} (hS : volume (frontier S)=0) : interior S=ᵐ[volume] S := by
  have hn : ∀ᵐp : ℝ×ℝ,p∉frontier S := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hS
  filter_upwards [hn] with p hp
  apply propext
  constructor
  · intro hx
    exact interior_subset hx
  · intro hx
    by_contra hn
    exact hp ⟨subset_closure hx,hn⟩

end PolygonArea
end PolygonJordan

end SimpleAmenable
end
end

end OAI
