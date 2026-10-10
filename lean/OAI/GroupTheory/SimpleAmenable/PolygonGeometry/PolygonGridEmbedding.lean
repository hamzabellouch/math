import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.TupleChartDomain
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonGroupoid
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonTrackArea

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonGridEmbedding
open Classical Set
namespace PolygonGrid

noncomputable def rectangle (a : ℕ) (r : CutRing) (i j : ℕ) : polygonAlgebra a :=
  ⟨(halfPlane a 0 (r*(i+1)) ∩ (halfPlane a 0 (r*i))ᶜ) ∩
    (halfPlane a 1 (r*(j+1)) ∩ (halfPlane a 1 (r*j))ᶜ),
    BooleanSubalgebra.inf_mem
      (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))
      (BooleanSubalgebra.inf_mem (halfPlane_mem _ _ _) (BooleanSubalgebra.compl_mem (halfPlane_mem _ _ _)))⟩

@[simp] theorem mem_rectangle (a : ℕ) (r : CutRing) (i j : ℕ) (x : GenericSquare a) :
    x∈(rectangle a r i j).val ↔
      x.val.1∈interval (ordinary r) i ∧ x.val.2∈interval (ordinary r) j := by
  simp only [rectangle,halfPlane,interval,Set.mem_inter_iff,Set.mem_compl_iff,
    Set.mem_ofPred_eq,Set.mem_Ico,cutForm,Matrix.cons_val_zero,Matrix.cons_val_one,
    map_mul,map_add,map_natCast,map_one,not_lt]
  tauto

noncomputable def displacement {m N : ℕ} (r : CutRing) (i j : Index m N) : CutRing×CutRing :=
  (r*((j.2.1.val:CutRing)-i.2.1.val),r*((j.2.2.val:CutRing)-i.2.2.val))

theorem displacement_mem_cell {m N : ℕ} (r : CutRing) (i j : Index m N)
    {x : ℝ×ℝ} (hx : (i.1.val,x)∈cell (ordinary r) i) :
    (j.1.val,x+(ordinary (displacement r i j).1,ordinary (displacement r i j).2))∈
      cell (ordinary r) j := by
  refine ⟨rfl,?_,?_⟩
  · have hxi := hx.2.1
    change ordinary r*i.2.1.val ≤ x.1 ∧ x.1 < ordinary r*(i.2.1.val+1) at hxi
    change ordinary r*j.2.1.val ≤ x.1+ordinary (displacement r i j).1 ∧
      x.1+ordinary (displacement r i j).1 < ordinary r*(j.2.1.val+1)
    simp only [displacement,map_mul,map_sub,map_natCast]
    constructor <;> nlinarith [hxi.1,hxi.2]
  · have hxi := hx.2.2
    change ordinary r*i.2.2.val ≤ x.2 ∧ x.2 < ordinary r*(i.2.2.val+1) at hxi
    change ordinary r*j.2.2.val ≤ x.2+ordinary (displacement r i j).2 ∧
      x.2+ordinary (displacement r i j).2 < ordinary r*(j.2.2.val+1)
    simp only [displacement,map_mul,map_sub,map_natCast]
    constructor <;> nlinarith [hxi.1,hxi.2]

theorem translate_displacement_mem {a m N : ℕ} (r : CutRing) (i j : Index m N)
    {x : GenericSquare a} (hx : (i.1.val,x.val)∈cell (ordinary r) i)
    (hj : cell (ordinary r) j⊆region m) :
    (j.1.val,(translate a (displacement r i j) x).val)∈cell (ordinary r) j := by
  have hd := displacement_mem_cell r i j hx
  have hs := hj hd
  have he : (translate a (displacement r i j) x).val =
      x.val+(ordinary (displacement r i j).1,ordinary (displacement r i j).2) := by
    apply Prod.ext
    · exact Int.fract_eq_self.mpr hs.2.1
    · exact Int.fract_eq_self.mpr hs.2.2
  rwa [he]

theorem exists_grid_side {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℕ, 0 < ordinary (shrinkingLevel b) ∧ ordinary (shrinkingLevel b)<δ := by
  have hp : 0 < Real.goldenRatio-1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hlt : Real.goldenRatio-1<1 := by linarith [Real.goldenRatio_lt_two]
  obtain ⟨b,hb⟩ := exists_pow_lt_of_lt_one hδ hlt
  refine ⟨b,(shrinkingLevel_bounds b).1,?_⟩
  rw [ordinary_shrinkingLevel,pow_succ]
  exact (mul_le_of_le_one_right (pow_nonneg hp.le _) hlt.le).trans_lt hb

end PolygonGrid
end PolygonGridEmbedding

section PolygonStrictComparison
open Classical Set
namespace PolygonGrid

theorem strict_comparison {a m : ℕ} (U V : Fin m → polygonAlgebra a)
    (harea : (∑i,PolygonArea.area (U i)) < ∑i,PolygonArea.area (V i)) :
    ∃ f : (PolygonObject.mk m U).Point ↪ (PolygonObject.mk m V).Point,
      PolygonObject.HasTable f := by
  let PU : PolygonObject a := ⟨m,U⟩
  let PV : PolygonObject a := ⟨m,V⟩
  obtain ⟨S,hS,heS,hcS,hiS⟩ := bank_representative U
  obtain ⟨T,hT,heT,hcT,hiT⟩ := bank_representative V
  have hh : MeasureTheory.Measure.count.prod ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod
       MeasureTheory.volume) (closure S) < μ (interior T) := by
    change μ (closure S)<μ (interior T)
    rwa [hcS,hiT]
  obtain ⟨δ,hδ,hmatch⟩ := strict_grid_comparison hS hT hh
  obtain ⟨b,hr,hrδ⟩ := exists_grid_side hδ
  let r := shrinkingLevel b
  obtain ⟨N,I,J,⟨route⟩,hcover,hinto⟩ := hmatch (ordinary r) hr hrδ
  have getsrc (p : PU.Point) : ∃i : I,(p.val.1.val,p.val.2.val)∈cell (ordinary r) i.val := by
    have hs : (p.val.1.val,p.val.2.val)∈S := (heS p.val.1 p.val.2).mpr p.property
    obtain ⟨i,hi,hp⟩ := Set.mem_iUnion₂.mp (hcover hs)
    exact ⟨⟨i,hi⟩,hp⟩
  choose src hsrc using getsrc
  have src_eq (p : PU.Point) (i : I) (hi : (p.val.1.val,p.val.2.val)∈cell (ordinary r) i.val) :
      src p=i := by
    apply Subtype.ext
    by_contra hn
    exact Set.disjoint_left.mp (cells_disjoint hr hn) (hsrc p) hi
  let out (p : PU.Point) : TrackPoint a m :=
    ((route (src p)).val.1,translate a (displacement r (src p).val (route (src p)).val) p.val.2)
  have houtCell (p : PU.Point) : ( (out p).1.val,(out p).2.val)∈
      cell (ordinary r) (route (src p)).val := by
    apply translate_displacement_mem r _ _ ⟨rfl,(hsrc p).2⟩
    exact Set.Subset.trans (hinto _ (route (src p)).property) hT
  have houtV (p : PU.Point) : (out p).2∈(V (out p).1).val := by
    apply (heT _ _).mp
    exact hinto _ (route (src p)).property (houtCell p)
  have hout_inj : Function.Injective out := by
    intro p q hpq
    have ht : (route (src p)).val=(route (src q)).val := by
      by_contra hn
      exact Set.disjoint_left.mp (cells_disjoint hr hn) (houtCell p)
        (by simpa only [hpq] using houtCell q)
    have hs : src p=src q := route.injective (Subtype.ext ht)
    have htrack : p.val.1=q.val.1 := by
      apply Fin.ext
      exact (hsrc p).1.trans (by simpa only [hs] using (hsrc q).1.symm)
    have hpoint : p.val.2=q.val.2 := by
      have he := congrArg Prod.snd hpq
      change translate a (displacement r (src p).val (route (src p)).val) p.val.2 =
        translate a (displacement r (src q).val (route (src q)).val) q.val.2 at he
      rw [hs] at he
      exact (translation a _).injective he
    exact Subtype.ext (Prod.ext htrack hpoint)
  let f : PU.Point ↪ PV.Point :=
    ⟨fun p => ⟨out p,houtV p⟩,fun _ _ h => hout_inj (congrArg Subtype.val h)⟩
  let chart (i : I) : PolygonObject.Chart (a:=a) m m :=
    ⟨i.val.1,(route i).val.1,displacement r i.val (route i).val,
      U i.val.1 ⊓ rectangle a r i.val.2.1.val i.val.2.2.val⟩
  refine ⟨f,Finset.univ.image chart,?_,?_⟩
  · intro c hc
    obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hc
    intro x hx
    change x∈(U i.val.1).val ∧ x∈(rectangle a r i.val.2.1.val i.val.2.2.val).val at hx
    refine ⟨hx.1,?_⟩
    have hcell : (i.val.1.val,x.val)∈cell (ordinary r) i.val :=
      ⟨rfl,(mem_rectangle a r _ _ x).mp hx.2⟩
    have hs := src_eq ⟨(i.val.1,x),hx.1⟩ i hcell
    change out ⟨(i.val.1,x),hx.1⟩ = ((route i).val.1,translate a (displacement r i.val (route i).val) x)
    simp only [out,hs]
  · intro p
    refine ⟨chart (src p),Finset.mem_image.mpr ⟨src p,Finset.mem_univ _,rfl⟩,?_,?_⟩
    · exact Fin.ext (hsrc p).1
    · change p.val.2∈(U (src p).val.1).val ∧
        p.val.2∈(rectangle a r (src p).val.2.1.val (src p).val.2.2.val).val
      refine ⟨?_,(mem_rectangle a r _ _ _).mpr (hsrc p).2⟩
      have ht : p.val.1=(src p).val.1 := Fin.ext (hsrc p).1
      simpa only [←ht] using p.property

end PolygonGrid
end PolygonStrictComparison

end SimpleAmenable
end
end

end OAI
