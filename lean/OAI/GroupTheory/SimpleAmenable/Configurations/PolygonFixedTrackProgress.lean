import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.WholeCoverCentrality
import OAI.GroupTheory.SimpleAmenable.Amenability.SubgroupTestReiter

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonFixedTrackProgress

theorem source_radius_valid : 0<ordinary (2-cutTau) ∧ ordinary (2-cutTau)<1/2 := by
  simp only [map_sub,map_ofNat,ordinary_cutTau]
  constructor
  · linarith [Real.goldenRatio_lt_two]
  · have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
    have hp := Real.sqrt_nonneg (5:ℝ)
    change 2-(1+Real.sqrt 5)/2<1/2
    nlinarith

theorem fixed_track_polygon_progress :
    ∃ a : ℕ, 0 < a ∧
      ∀ m : ℕ, 100 ≤ m →
        Infinite (polygonAlternatingGroup a m) ∧
        IsSimpleGroup (polygonAlternatingGroup a m) ∧
        FolnerAmenable (polygonAlternatingGroup a m) ∧
        ∃ (H : Type) (_ : Group H) (q : H →* polygonAlternatingGroup a m),
          Group.IsFinitelyPresented H ∧ Function.Surjective q ∧ q.ker ≤ Subgroup.center H := by
  obtain ⟨a,ha,hSlope,hConj⟩ := exists_source_slope_explicit
  refine ⟨a,ha,fun m hm => ?_⟩
  obtain ⟨n,rfl⟩ : ∃n,m=n+1 := ⟨m-1,by omega⟩
  obtain ⟨hinf,hsimple,hfol⟩ := polygon_infinite_simple_folner ha (by omega : 15≤n+1)
  obtain ⟨L,hpres,hsur,hcent⟩ := polygon_central_cover (by omega : 2≤n) ha hm
    source_radius_valid (by linarith : 8000<ordinary (cutTau^a)) hConj
  exact ⟨hinf,hsimple,hfol,BoundedRelationCover L (alternatingGenerator a (2-cutTau) n (by omega)),
    inferInstance,coverMap L (alternatingGenerator a (2-cutTau) n (by omega)),hpres,hsur,hcent⟩

end PolygonFixedTrackProgress

section PolygonConfigurations
open Classical Set

structure PolygonPlacement (a m : ℕ) where
  toEmbedding : GenericSquare a ↪ TrackPoint a m
  charts : ∃s : Finset (Fin m × (CutRing×CutRing) × polygonAlgebra a),
    (∀c∈s,∀x∈c.2.2.val,toEmbedding x=(c.1,translate a c.2.1 x)) ∧
    ∀x,∃c∈s,x∈c.2.2.val

namespace PolygonPlacement
variable {a m : ℕ}
instance : CoeFun (PolygonPlacement a m) (fun _ => GenericSquare a → TrackPoint a m) :=
  ⟨fun f => f.toEmbedding⟩

@[ext] theorem ext {f g : PolygonPlacement a m} (h : ∀x,f x=g x) : f=g := by
  cases f; cases g
  congr
  exact Function.Embedding.ext h

noncomputable def standard (i : Fin m) : PolygonPlacement a m where
  toEmbedding := ⟨fun x => (i,x),fun _ _ h => congrArg Prod.snd h⟩
  charts := by
    refine ⟨{(i,0,⊤)},?_,?_⟩
    · intro c hc x _
      obtain rfl := Finset.mem_singleton.mp hc
      change (i,x)=(i,translate a 0 x)
      rw [translate_zero]
    · intro x
      exact ⟨(i,0,⊤),Finset.mem_singleton_self _,by trivial⟩

@[simp] theorem standard_apply (i : Fin m) (x : GenericSquare a) :
    standard i x=(i,x) := rfl

noncomputable def postcompose (g : polygonFullGroup a m) (f : PolygonPlacement a m) :
    PolygonPlacement a m where
  toEmbedding := ⟨fun x => g.val (f x),g.val.injective.comp f.toEmbedding.injective⟩
  charts := by
    obtain ⟨s,hs,hcover⟩ := g.property
    obtain ⟨t,ht,tcover⟩ := f.charts
    let pairs := (s×ˢt).filter (fun cd => cd.1.source=cd.2.1)
    let conv : TableChart a m × (Fin m × (CutRing×CutRing) × polygonAlgebra a) →
        Fin m × (CutRing×CutRing) × polygonAlgebra a := fun cd =>
      (cd.1.target,cd.1.shift+cd.2.2.1,
        ⟨cd.2.2.2.val ∩ translate a cd.2.2.1 ⁻¹' cd.1.domain.val,
          BooleanSubalgebra.inf_mem cd.2.2.2.property
            (polygon_preimage_translate cd.2.2.1 cd.1.domain.property)⟩)
    refine ⟨pairs.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨⟨d,e⟩,hde,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hde
      obtain ⟨hd,he'⟩ := Finset.mem_product.mp hp
      intro x hx
      change g.val (f x)=(d.target,translate a (d.shift+e.2.1) x)
      rw [ht e he' x hx.1,←he,hs d hd _ hx.2,translate_add]
    · intro x
      obtain ⟨e,he,hx⟩ := tcover x
      obtain ⟨d,hd,hfx⟩ := hcover (f x)
      have hf := ht e he x hx
      have hmatch : d.source=e.1 := hfx.1.symm.trans (congrArg Prod.fst hf)
      refine ⟨conv (d,e),Finset.mem_image.mpr ⟨(d,e),?_,rfl⟩,hx,?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hd,he⟩,hmatch⟩
      · change translate a e.2.1 x∈d.domain.val
        simpa only [hf] using hfx.2

@[simp] theorem postcompose_apply (g : polygonFullGroup a m) (f : PolygonPlacement a m)
    (x : GenericSquare a) : postcompose g f x=g.val (f x) := rfl

noncomputable instance : MulAction (polygonFullGroup a m) (PolygonPlacement a m) where
  smul := postcompose
  one_smul _ := by apply PolygonPlacement.ext; intro _; rfl
  mul_smul _ _ _ := by apply PolygonPlacement.ext; intro _; rfl

@[simp] theorem smul_apply (g : polygonFullGroup a m) (f : PolygonPlacement a m)
    (x : GenericSquare a) : (g • f) x=g.val (f x) := rfl

theorem range_fiber_polygon (f : PolygonPlacement a m) (i : Fin m) :
    {x | (i,x)∈Set.range f}∈polygonAlgebra a := by
  obtain ⟨s,hs,hcover⟩ := f.charts
  have he : {x | (i,x)∈Set.range f}=
      ⋃c∈s.filter (fun c => c.1=i),translation a c.2.1 '' c.2.2.val := by
    ext y
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨c,hc,hxc⟩ := hcover x
      have h := (hs c hc x hxc).symm.trans hx
      exact Set.mem_iUnion.mpr ⟨c,Set.mem_iUnion.mpr ⟨
        Finset.mem_filter.mpr ⟨hc,congrArg Prod.fst h⟩,
        ⟨x,hxc,congrArg Prod.snd h⟩⟩⟩
    · intro hy
      obtain ⟨c,hc,hy⟩ := Set.mem_iUnion₂.mp hy
      obtain ⟨x,hx,hxy⟩ := hy
      refine ⟨x,?_⟩
      rw [hs c (Finset.mem_filter.mp hc).1 x hx,(Finset.mem_filter.mp hc).2]
      exact Prod.ext rfl hxy
  rw [he]
  apply BooleanSubalgebra.biSup_mem (Finset.finite_toSet _)
  intro chart _
  exact polygon_image_translation _ chart.2.2.property

def Apart (f g : PolygonPlacement a m) : Prop := Disjoint (Set.range f) (Set.range g)

theorem apart_symm {f g : PolygonPlacement a m} (h : Apart f g) : Apart g f := h.symm

theorem apart_iff (f g : PolygonPlacement a m) : Apart f g ↔ ∀x y,f x≠g y := by
  constructor
  · intro h x y he
    exact Set.disjoint_left.mp h ⟨x,rfl⟩ ⟨y,he.symm⟩
  · intro h
    apply Set.disjoint_left.mpr
    rintro _ ⟨x,rfl⟩ ⟨y,he⟩
    exact h x y he.symm

theorem apart_smul_iff (h : polygonFullGroup a m) (f g : PolygonPlacement a m) :
    Apart (h • f) (h • g) ↔ Apart f g := by
  simp only [apart_iff,smul_apply,h.val.injective.ne_iff]

theorem standard_apart {i j : Fin m} (hij : i≠j) :
    Apart (standard (a:=a) i) (standard j) := by
  rw [apart_iff]
  intro _ _ equality
  exact hij (congrArg Prod.fst equality)

noncomputable def bank {n : ℕ} (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) : TrackPoint a n ↪ TrackPoint a m where
  toFun x := f x.1 x.2
  inj' := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hij : i=j := by
      by_contra hn
      exact (apart_iff _ _).mp (hf hn) x y he
    subst j
    exact Prod.ext rfl ((f i).toEmbedding.injective he)

end PolygonPlacement
end PolygonConfigurations

end SimpleAmenable
end
end

end OAI
