import OAI.Analysis.LipschitzHilbert.Estimates.ComparableCommutatorSum

namespace OAI

/-! Exact finite linearity identities for the actual Schwartz commutator. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_sum_right {ι : Type*} (I : Finset ι)
    (b : SchwartzMap ℝ ℂ) (h : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzProduct b (∑ i∈I, h i)=∑ i∈I, lineSchwartzProduct b (h i) := by
  ext x
  simp only [lineSchwartzProduct_apply,sum_apply,Finset.mul_sum]

theorem lineSchwartzProduct_sum_left {ι : Type*} (I : Finset ι)
    (b : ι → SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ) :
    lineSchwartzProduct (∑ i∈I, b i) h=∑ i∈I, lineSchwartzProduct (b i) h := by
  ext x
  simp only [lineSchwartzProduct_apply,sum_apply,Finset.sum_mul]

theorem lineSchwartzCommutator_sum_right {ι : Type*} (I : Finset ι)
    (m b : SchwartzMap ℝ ℂ) (h : ι → SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m b (∑ i∈I, h i)=∑ i∈I, lineSchwartzCommutator m b (h i) := by
  simp only [lineSchwartzCommutator,lineSchwartzProjection_sum,lineSchwartzProduct_sum_right,
    Finset.sum_sub_distrib]

theorem lineSchwartzCommutator_sum_left {ι : Type*} (I : Finset ι)
    (m : SchwartzMap ℝ ℂ) (b : ι → SchwartzMap ℝ ℂ) (h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (∑ i∈I, b i) h=∑ i∈I, lineSchwartzCommutator m (b i) h := by
  simp only [lineSchwartzCommutator,lineSchwartzProduct_sum_left,lineSchwartzProjection_sum,
    Finset.sum_sub_distrib]

theorem lineSchwartzCommutator_add_left (m b c h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (b+c) h=
      lineSchwartzCommutator m b h+lineSchwartzCommutator m c h := by
  have hprod (f g p : SchwartzMap ℝ ℂ) : lineSchwartzProduct (f+g) p=
      lineSchwartzProduct f p+lineSchwartzProduct g p := by
    ext x
    simp only [lineSchwartzProduct_apply,add_apply,add_mul]
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f+g)=
      lineSchwartzProjection m 1 (by norm_num) f+lineSchwartzProjection m 1 (by norm_num) g :=
    map_add (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hprod,hproj]
  abel

theorem lineSchwartzCommutator_zero_left (m h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m 0 h=0 := by
  ext x
  have hp : lineSchwartzProduct (0 : SchwartzMap ℝ ℂ) h=0 := by ext y; simp
  have hT : lineSchwartzProjection m 1 (by norm_num) (0 : SchwartzMap ℝ ℂ)=0 :=
    map_zero (lineSchwartzProjectionLM m 1 (by norm_num))
  simp only [lineSchwartzCommutator,lineSchwartzProduct_apply,zero_apply,zero_mul,hp,hT,sub_zero]

theorem lineSchwartzCommutator_sub_left (m b c h : SchwartzMap ℝ ℂ) :
    lineSchwartzCommutator m (b-c) h=
      lineSchwartzCommutator m b h-lineSchwartzCommutator m c h := by
  have hprod (f g p : SchwartzMap ℝ ℂ) : lineSchwartzProduct (f-g) p=
      lineSchwartzProduct f p-lineSchwartzProduct g p := by
    ext x
    simp only [lineSchwartzProduct_apply,sub_apply,sub_mul]
  have hproj (f g : SchwartzMap ℝ ℂ) : lineSchwartzProjection m 1 (by norm_num) (f-g)=
      lineSchwartzProjection m 1 (by norm_num) f-lineSchwartzProjection m 1 (by norm_num) g :=
    map_sub (lineSchwartzProjectionLM m 1 (by norm_num)) f g
  simp only [lineSchwartzCommutator,hprod,hproj]
  abel

end LipschitzHilbert.PacketRepresentation

end

end OAI
