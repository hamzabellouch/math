import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Supported
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonArea

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAreaAlgebra

open Classical Set MeasureTheory
namespace PolygonArea

@[simp] theorem area_bot (a : ℕ) : area (⊥ : polygonAlgebra a)=0 := by
  change volume ((fun point : GenericSquare a => point.val) '' (∅ : Set (GenericSquare a)))=0
  simp

theorem area_mono {a : ℕ} {U V : polygonAlgebra a} (h : U≤V) : area U≤area V :=
  measure_mono (Set.image_mono h)

theorem area_eq_sum {a : ℕ} {ι : Type*} [Fintype ι] (U : polygonAlgebra a)
    (f : ι → polygonAlgebra a) (he : U.val=⋃i,(f i).val)
    (hd : Pairwise (fun i j => Disjoint (f i).val (f j).val)) :
    area U=∑i,area (f i) := by
  have hd' : Pairwise (fun i j =>
      Disjoint ((fun point : GenericSquare a => point.val) '' (f i).val)
        ((fun point : GenericSquare a => point.val) '' (f j).val)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    have : y=x := Subtype.ext hyx
    exact Set.disjoint_left.mp (hd hij) hx (by simpa only [this] using hy)
  change volume ((fun point : GenericSquare a => point.val) '' U.val)=_
  rw [he,Set.image_iUnion,measure_iUnion hd' (fun i => measurable_image (f i)),tsum_fintype]
  rfl

theorem area_sup_add_inf {a : ℕ} (U V : polygonAlgebra a) :
    area (U⊔V)+area (U⊓V)=area U+area V := by
  change volume ((fun point : GenericSquare a => point.val) '' (U.val∪V.val))+
    volume ((fun point : GenericSquare a => point.val) '' (U.val∩V.val))=_
  rw [Set.image_union,Set.image_inter (f := fun point : GenericSquare a => point.val)
    Subtype.val_injective]
  exact measure_union_add_inter _ (measurable_image V)

theorem area_compl {a : ℕ} (U : polygonAlgebra a) : area U+area Uᶜ=1 := by
  have h := area_sup_add_inf U Uᶜ
  simpa only [sup_compl_eq_top,inf_compl_eq_bot,area_top,area_bot,add_zero] using h.symm

theorem area_sup_le {a : ℕ} (U V : polygonAlgebra a) : area (U⊔V)≤area U+area V := by
  change volume ((fun point : GenericSquare a => point.val) '' (U.val∪V.val))≤_
  rw [Set.image_union]
  exact measure_union_le _ _

theorem area_finset_sup_le {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    area (s.sup f)≤∑i∈s,area (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    exact (area_sup_le _ _).trans (add_le_add le_rfl ih)

theorem area_translation_wrap {a : ℕ} (u : CutRing×CutRing) (k : ℤ×ℤ)
    (U : polygonAlgebra a) (hU : U.val⊆wrapCell a u k) :
    area (translatedPolygon u U)=area U := by
  let v : ℝ×ℝ := (ordinary (u.1-(k.1:CutRing)),ordinary (u.2-(k.2:CutRing)))
  have he : Subtype.val '' (translatedPolygon u U).val=
      (fun p : ℝ×ℝ => p+v) '' (Subtype.val '' U.val) := by
    ext p
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,(translate_on_wrap u k (hU hx)).symm⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨translate a u x,⟨x,hx,rfl⟩,translate_on_wrap u k (hU hx)⟩
  change volume (Subtype.val '' (translatedPolygon u U).val)=_
  rw [he,Set.image_add_right,measure_preimage_add_right]
  rfl

theorem area_translation {a : ℕ} (u : CutRing×CutRing) (U : polygonAlgebra a) :
    area (translatedPolygon u U)=area U := by
  let W (k : wrapIndices u) : polygonAlgebra a :=
    U ⊓ ⟨wrapCell a u k.val,wrapCell_mem a u k.val⟩
  have hcov : U.val=⋃k,(W k).val := by
    ext x
    constructor
    · intro hx
      let k : wrapIndices u := ⟨(⌊x.val.1+ordinary u.1⌋,⌊x.val.2+ordinary u.2⌋),point_wrap_mem u x⟩
      exact Set.mem_iUnion.mpr ⟨k,hx,(mem_wrapCell u k.val x).mpr ⟨rfl,rfl⟩⟩
    · intro hx
      obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
      exact hk.1
  have hdis : Pairwise (fun k l : wrapIndices u => Disjoint (W k).val (W l).val) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hx₁,hx₂⟩ := (mem_wrapCell u k.val x).mp hx.2
    obtain ⟨hy₁,hy₂⟩ := (mem_wrapCell u l.val x).mp hy.2
    exact hkl (Subtype.ext (Prod.ext (hx₁.symm.trans hy₁) (hx₂.symm.trans hy₂)))
  have he : (translatedPolygon u U).val=⋃k,(translatedPolygon u (W k)).val := by
    change translation a u '' U.val=⋃k,translation a u '' (W k).val
    rw [hcov,Set.image_iUnion]
  have hd : Pairwise (fun k l : wrapIndices u =>
      Disjoint (translatedPolygon u (W k)).val (translatedPolygon u (W l)).val) := by
    intro k l hkl
    apply Set.disjoint_image_image
    intro x hx y hy he
    have heq := (translation a u).injective he
    subst y
    exact Set.disjoint_left.mp (hdis hkl) hx hy
  rw [area_eq_sum _ _ he hd,area_eq_sum _ _ hcov hdis]
  exact Finset.sum_congr rfl (fun k _ => area_translation_wrap u k.val (W k) (fun _ hx => hx.2))

end PolygonArea
end PolygonAreaAlgebra

end SimpleAmenable
end
end

end OAI
