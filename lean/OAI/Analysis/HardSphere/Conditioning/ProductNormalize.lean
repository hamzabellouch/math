import Mathlib
import OAI.Analysis.HardSphere.Conditioning.ProductExpose

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {I : Type*} [Fintype I] {X : I→Type*} [∀i,MeasurableSpace (X i)]

def conditionedMeasure {A : Type*} [MeasurableSpace A] (μ : Measure A) (S : Set A) : Measure A :=
  (μ S)⁻¹ • μ.restrict S

lemma conditioned_probability {A : Type*} [MeasurableSpace A] (μ : Measure A) [IsFiniteMeasure μ]
    {S : Set A} (h : μ S≠0) : IsProbabilityMeasure (conditionedMeasure μ S) := by
  constructor
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel h (measure_ne_top _ _)

lemma pi_conditioned (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (hS : ∀i,MeasurableSet (S i)) (hpos : ∀i,ν i (S i)≠0) :
    Measure.pi (fun i ↦ conditionedMeasure (ν i) (S i))=
      conditionedMeasure (Measure.pi ν) (univ.pi S) := by
  let : ∀i,IsProbabilityMeasure (conditionedMeasure (ν i) (S i)) := fun i ↦ conditioned_probability (ν i) (hpos i)
  apply Measure.pi_eq
  intro B hB
  simp only [conditionedMeasure,Measure.smul_apply,smul_eq_mul]
  rw [Measure.restrict_apply (MeasurableSet.univ_pi hB),←Set.pi_inter_distrib,Measure.pi_pi,Measure.pi_pi]
  simp_rw [Measure.restrict_apply' (hS _)]
  rw [Finset.prod_mul_distrib]
  congr 1
  exact ENNReal.prod_inv_distrib (fun i _ j _ _ ↦ Or.inl (hpos i))

lemma condition_product_factorization (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (S : ∀i,Set (X i)) (hS : ∀i,MeasurableSet (S i)) (hpos : ∀i,ν i (S i)≠0)
    (B : Set (∀i,X i)) (hB : MeasurableSet B) (hfull : (Measure.pi ν) (B∩univ.pi S)≠0) :
    conditionedMeasure (Measure.pi ν) (B∩univ.pi S)=
      conditionedMeasure (Measure.pi (fun i ↦ conditionedMeasure (ν i) (S i))) B := by
  rw [pi_conditioned ν S hS hpos]
  let μ := Measure.pi ν
  have hz : μ (univ.pi S)≠0 := by
    change (Measure.pi ν) (univ.pi S)≠0
    exact ne_of_gt ((pos_iff_ne_zero.mpr hfull).trans_le (measure_mono inter_subset_right))
  have hzinf : μ (univ.pi S)≠⊤ := measure_ne_top _ _
  unfold conditionedMeasure
  rw [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hB,Measure.restrict_smul,
    Measure.restrict_restrict hB,smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inr (measure_ne_top _ _)) (Or.inl (ENNReal.inv_ne_top.mpr hz)),inv_inv]
  change (μ (B∩univ.pi S))⁻¹=μ (univ.pi S)*(μ (B∩univ.pi S))⁻¹*(μ (univ.pi S))⁻¹
  rw [mul_comm (μ (univ.pi S)),mul_assoc,ENNReal.mul_inv_cancel hz hzinf,mul_one]

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
variable {E I J : Type*} [MeasurableSpace E] [Fintype I] [Fintype J]
variable {X : I→Type*} [∀i,MeasurableSpace (X i)]

lemma restrict_finite_partition {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (B : Set A) (F : J→Set A) (hF : ∀j,MeasurableSet (F j))
    (hdis : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (hcover : (⋃j,F j)=univ) :
    ∑ j,(μ.restrict (B∩F j))=μ.restrict B := by
  have h := (μ.restrict B).restrict_iUnion hdis hF
  rw [hcover,Measure.restrict_univ,Measure.sum_fintype] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.restrict_restrict (hF j),inter_comm]

lemma masked_exposure_reconstruct (μ : Measure E) [SFinite μ]
    (ν : ∀i,Measure (X i)) [∀i,IsProbabilityMeasure (ν i)]
    (p : J→I→Prop) [∀j,DecidablePred (p j)]
    {B : Set (E×(∀i,X i))} (hB : MeasurableSet B)
    (F : J→Set (E×(∀i,X i))) (hF : ∀j,MeasurableSet (F j))
    (hdis : Pairwise (fun i j ↦ Disjoint (F i) (F j))) (hcover : (⋃j,F j)=univ)
    [∀j,SFinite (exposedLaw μ ν (p j) (B∩F j))] :
    (∑j,((exposedLaw μ ν (p j) (B∩F j)).compProd
      (fiberNormalize (Kernel.const _ (Measure.pi fun i : {i // p j i} ↦ ν i))
        (blockEvent (p j) (B∩F j)))).map (blockGlue (p j)))=(μ.prod (Measure.pi ν)).restrict B := by
  simp_rw [exposed_block_reconstruct μ ν _ (hB.inter (hF _))]
  exact restrict_finite_partition _ B F hF hdis hcover

def flagEvent (f : ∀i,E×X i→Bool) (b : I→Bool) : Set (E×(∀i,X i)) :=
  {z | ∀i,f i (z.1,z.2 i)=b i}

lemma flagEvent_measurable (f : ∀i,E×X i→Bool) (hf : ∀i,Measurable (f i)) (b : I→Bool) :
    MeasurableSet (flagEvent f b) := by
  have he : flagEvent f b=⋂i,{z : E×(∀i,X i) | f i (z.1,z.2 i)=b i} := by ext z; simp [flagEvent]
  rw [he]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_eq_fun ((hf i).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))) measurable_const

omit [MeasurableSpace E] [Fintype I] [∀i,MeasurableSpace (X i)] in
lemma flagEvent_partition (f : ∀i,E×X i→Bool) :
    Pairwise (fun b c ↦ Disjoint (flagEvent f b) (flagEvent f c)) ∧ (⋃b,flagEvent f b)=univ := by
  constructor
  · intro b c hbc
    apply Set.disjoint_left.mpr
    intro z hb hc
    apply hbc
    funext i
    exact (hb i).symm.trans (hc i)
  · apply eq_univ_of_forall
    intro z
    exact mem_iUnion.mpr ⟨fun i ↦ f i (z.1,z.2 i),fun _ ↦ rfl⟩

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_inside (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) (i : {i // p i}) :
    (blockGlue p (w,v)).2 i=v i := by
  simp [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,i.property]

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_outside (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) (i : {i // ¬p i}) :
    (blockGlue p (w,v)).2 i=w.2 i := by
  simp [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,i.property]

omit [MeasurableSpace E] [Fintype I] in
lemma blockGlue_fst (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) :
    (blockGlue p (w,v)).1=w.1 := rfl

omit [MeasurableSpace E] [Fintype I] in
lemma flag_fiber_iff (f : ∀i,E×X i→Bool) (b : I→Bool)
    (p : I→Prop) [DecidablePred p]
    (w : E×(∀i : {i // ¬p i},X i)) (v : ∀i : {i // p i},X i) :
    blockGlue p (w,v)∈flagEvent f b ↔
      (∀i : {i // ¬p i},f i (w.1,w.2 i)=b i) ∧
      (∀i : {i // p i},f i (w.1,v i)=b i) := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [blockGlue_fst,blockGlue_outside] using h i
    · intro i
      simpa only [blockGlue_fst,blockGlue_inside] using h i
  · rintro ⟨hout,hin⟩ i
    by_cases hi : p i
    · simpa [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,hi] using hin ⟨i,hi⟩
    · simpa [blockGlue,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,hi] using hout ⟨i,hi⟩

end HardSphere.Comparison

end
end

end

end OAI
