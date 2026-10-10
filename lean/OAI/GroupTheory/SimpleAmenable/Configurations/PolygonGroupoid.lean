import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackPoint

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open Classical Set CategoryTheory

structure PolygonObject (a : ℕ) where
  tracks : ℕ
  cell : Fin tracks → polygonAlgebra a

namespace PolygonObject
variable {a : ℕ}

abbrev Point (U : PolygonObject a) := {x : TrackPoint a U.tracks // x.2 ∈ (U.cell x.1).val}

structure Chart (m n : ℕ) where
  source : Fin m
  target : Fin n
  shift : CutRing × CutRing
  domain : polygonAlgebra a

namespace Chart
variable {U V W : PolygonObject a}

def Holds (c : Chart (a:=a) U.tracks V.tracks) (f : U.Point → V.Point) : Prop :=
  ∀ x∈c.domain.val, ∃hx : x∈(U.cell c.source).val,
    (f ⟨(c.source,x),hx⟩).val=(c.target,translate a c.shift x)

def Contains (c : Chart (a:=a) U.tracks V.tracks) (x : U.Point) : Prop :=
  x.val.1=c.source ∧ x.val.2∈c.domain.val

noncomputable def comp (c : Chart (a:=a) V.tracks W.tracks)
    (d : Chart (a:=a) U.tracks V.tracks) : Chart (a:=a) U.tracks W.tracks :=
  ⟨d.source,c.target,c.shift+d.shift,
    ⟨d.domain.val ∩ translate a d.shift ⁻¹' c.domain.val,
      BooleanSubalgebra.inf_mem d.domain.property (polygon_preimage_translate d.shift c.domain.property)⟩⟩

theorem comp_holds {c : Chart (a:=a) V.tracks W.tracks}
    {d : Chart (a:=a) U.tracks V.tracks} {f : V.Point → W.Point} {g : U.Point → V.Point}
    (hc : c.Holds f) (hd : d.Holds g) (hmatch : c.source=d.target) :
    (c.comp d).Holds (f ∘ g) := by
  rintro x ⟨hx,hcx⟩
  obtain ⟨hu,he⟩ := hd x hx
  obtain ⟨hv,hf⟩ := hc (translate a d.shift x) hcx
  refine ⟨hu,?_⟩
  have hp : g ⟨(d.source,x),hu⟩=⟨(c.source,translate a d.shift x),hv⟩ := by
    apply Subtype.ext
    simpa only [hmatch] using he
  change (f (g ⟨(d.source,x),hu⟩)).val=(c.target,translate a (c.shift+d.shift) x)
  rw [hp,hf,translate_add]

noncomputable def inverse (c : Chart (a:=a) U.tracks V.tracks) :
    Chart (a:=a) V.tracks U.tracks :=
  ⟨c.target,c.source,-c.shift,
    ⟨translation a c.shift '' c.domain.val,polygon_image_translation _ c.domain.property⟩⟩

theorem inverse_holds (f : U.Point ≃ V.Point) {c : Chart (a:=a) U.tracks V.tracks}
    (hc : c.Holds f) : c.inverse.Holds f.symm := by
  rintro y ⟨x,hx,rfl⟩
  obtain ⟨hu,he⟩ := hc x hx
  have hv : translate a c.shift x∈(V.cell c.target).val := by
    have h := (f ⟨(c.source,x),hu⟩).property
    rw [he] at h
    exact h
  refine ⟨hv,?_⟩
  have hp : (⟨(c.target,translate a c.shift x),hv⟩ : V.Point)=f ⟨(c.source,x),hu⟩ :=
    Subtype.ext he.symm
  change (f.symm ⟨(c.target,translate a c.shift x),hv⟩).val =
    (c.source,translate a (-c.shift) (translate a c.shift x))
  rw [hp,f.symm_apply_apply,←translate_add,neg_add_cancel,translate_zero]

end Chart

def HasTable {U V : PolygonObject a} (f : U.Point → V.Point) : Prop :=
  ∃s : Finset (Chart (a:=a) U.tracks V.tracks),
    (∀c∈s,c.Holds f) ∧ ∀x,∃c∈s,c.Contains x

theorem identity_hasTable (U : PolygonObject a) : HasTable (id : U.Point → U.Point) := by
  let c : Fin U.tracks → Chart (a:=a) U.tracks U.tracks := fun i => ⟨i,i,0,U.cell i⟩
  refine ⟨Finset.univ.image c,?_,?_⟩
  · intro d hd
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hd
    intro x hx
    exact ⟨hx,by change (i,x)=(i,translate a 0 x); rw [translate_zero]⟩
  · intro x
    exact ⟨c x.val.1,Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩,rfl,x.property⟩

theorem comp_hasTable {U V W : PolygonObject a} {f : V.Point → W.Point} {g : U.Point → V.Point}
    (hf : HasTable f) (hg : HasTable g) : HasTable (f ∘ g) := by
  obtain ⟨s,hs,hcover⟩ := hf
  obtain ⟨t,ht,tcover⟩ := hg
  let pairs := (s×ˢt).filter (fun cd => cd.1.source=cd.2.target)
  refine ⟨pairs.image (fun cd => cd.1.comp cd.2),?_,?_⟩
  · intro e he
    obtain ⟨⟨c,d⟩,hcd,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hmem,hmatch⟩ := Finset.mem_filter.mp hcd
    obtain ⟨hc,hd⟩ := Finset.mem_product.mp hmem
    exact Chart.comp_holds (hs c hc) (ht d hd) hmatch
  · intro x
    obtain ⟨d,hd,hx⟩ := tcover x
    obtain ⟨c,hc,hgx⟩ := hcover (g x)
    obtain ⟨hu,he⟩ := ht d hd x.val.2 hx.2
    have hxval : (⟨(d.source,x.val.2),hu⟩ : U.Point)=x := by
      apply Subtype.ext
      exact Prod.ext hx.1.symm rfl
    rw [hxval] at he
    have hmatch : c.source=d.target := by
      change (g x).val.1=c.source ∧ (g x).val.2∈c.domain.val at hgx
      rw [he] at hgx
      exact hgx.1.symm
    refine ⟨c.comp d,Finset.mem_image.mpr ⟨(c,d),?_,rfl⟩,hx.1,hx.2,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hc,hd⟩,hmatch⟩
    · change translate a d.shift x.val.2∈c.domain.val
      simpa only [he] using hgx.2

theorem inverse_hasTable {U V : PolygonObject a} (f : U.Point ≃ V.Point)
    (hf : HasTable f) : HasTable f.symm := by
  obtain ⟨s,hs,hcover⟩ := hf
  refine ⟨s.image Chart.inverse,?_,?_⟩
  · intro c hc
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
    exact Chart.inverse_holds f (hs d hd)
  · intro y
    obtain ⟨c,hc,hx⟩ := hcover (f.symm y)
    obtain ⟨hu,he⟩ := hs c hc (f.symm y).val.2 hx.2
    have hp : (⟨(c.source,(f.symm y).val.2),hu⟩ : U.Point)=f.symm y := by
      apply Subtype.ext
      exact Prod.ext hx.1.symm rfl
    rw [hp,f.apply_symm_apply] at he
    refine ⟨c.inverse,Finset.mem_image.mpr ⟨c,hc,rfl⟩,?_,?_⟩
    · exact congrArg Prod.fst he
    · exact ⟨(f.symm y).val.2,hx.2,(congrArg Prod.snd he).symm⟩

structure Arrow (U V : PolygonObject a) where
  toEquiv : U.Point ≃ V.Point
  hasTable : HasTable toEquiv

@[ext] theorem Arrow.ext {U V : PolygonObject a} {f g : Arrow U V}
    (h : f.toEquiv=g.toEquiv) : f=g := by
  cases f; cases g; cases h; rfl

noncomputable instance : Groupoid (PolygonObject a) where
  Hom := Arrow
  id U := ⟨Equiv.refl _,identity_hasTable U⟩
  comp f g := ⟨f.toEquiv.trans g.toEquiv,comp_hasTable (f:=g.toEquiv) (g:=f.toEquiv) g.hasTable f.hasTable⟩
  id_comp f := Arrow.ext rfl
  comp_id f := Arrow.ext rfl
  assoc f g h := Arrow.ext rfl
  inv f := ⟨f.toEquiv.symm,inverse_hasTable f.toEquiv f.hasTable⟩
  inv_comp f := by apply Arrow.ext; exact Equiv.symm_trans_self _
  comp_inv f := by apply Arrow.ext; exact Equiv.self_trans_symm _

def Positional {U V : PolygonObject a} (f : U ⟶ V) : Prop :=
  ∀x,(f.toEquiv x).val.2=x.val.2

noncomputable def positionalSubgroupoid (a : ℕ) : Subgroupoid (PolygonObject a) where
  arrows U V := {f | Positional f}
  inv := by
    intro U V f hf y
    change (f.toEquiv.symm y).val.2=y.val.2
    have h := hf (f.toEquiv.symm y)
    simpa using h.symm
  mul := by
    intro U V W f hf g hg x
    exact (hg (f.toEquiv x)).trans (hf x)

theorem identity_positional (U : PolygonObject a) : Positional (𝟙 U) := fun _ => rfl

end PolygonObject

end SimpleAmenable

end OAI
