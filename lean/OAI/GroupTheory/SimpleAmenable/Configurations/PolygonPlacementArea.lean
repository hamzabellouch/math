import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ConfigurationResolution
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonGridEmbedding
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonAreaAlgebra

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonPlacementArea

open Classical Set
namespace PolygonArea

@[simp] theorem val_finset_sup {a : ℕ} {ι : Type*} (s : Finset ι) (f : ι → polygonAlgebra a) :
    (s.sup f).val=⋃i∈s,(f i).val := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sup_insert,BooleanSubalgebra.val_sup,ih]

end PolygonArea
namespace PolygonPlacement

noncomputable def imageBank {a m : ℕ} (f : PolygonPlacement a m) (i : Fin m) : polygonAlgebra a :=
  ⟨{x | (i,x)∈Set.range f},range_fiber_polygon f i⟩

theorem imageBank_area_le {a m : ℕ} (f : PolygonPlacement a m) :
    (∑i,PolygonArea.area (imageBank f i))≤1 := by
  obtain ⟨s,hs,hcover⟩ := f.charts
  let D : s → polygonAlgebra a := fun c => c.val.2.2
  obtain ⟨P,hP,hSup,hdisP⟩ := Fintype.exists_disjointed_le D
  have hcoverP : (⊤ : polygonAlgebra a).val=⋃c,(P c).val := by
    have hv := congrArg (fun A : polygonAlgebra a => A.val) hSup
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at hv
    rw [hv]
    ext x
    simp only [BooleanSubalgebra.val_top,Set.top_eq_univ,Set.mem_univ,true_iff,Set.mem_iUnion]
    obtain ⟨c,hc,hx⟩ := hcover x
    exact ⟨⟨c,hc⟩,hx⟩
  have hsumP : (∑c,PolygonArea.area (P c))=1 := by
    rw [←PolygonArea.area_top a]
    symm
    apply PolygonArea.area_eq_sum _ P hcoverP
    intro i j hij
    have h : Disjoint (P i) (P j) := hdisP hij
    rw [disjoint_iff] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr (congrArg (fun A : polygonAlgebra a => A.val) h)
  let Q (i : Fin m) (c : s) : polygonAlgebra a :=
    if c.val.1=i then translatedPolygon c.val.2.1 (P c) else ⊥
  have hbank (i : Fin m) : imageBank f i≤Finset.univ.sup (Q i) := by
    intro y hy
    obtain ⟨x,hxy⟩ := hy
    have hx : x∈⋃c,(P c).val := by rw [←hcoverP]; trivial
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    have he := (hs c.val c.property x (hP c hc)).symm.trans hxy
    have ht : c.val.1=i := congrArg Prod.fst he
    rw [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨c,Finset.mem_univ _,?_⟩
    simp only [Q,ht,ite_true]
    exact ⟨x,hc,congrArg Prod.snd he⟩
  calc
    (∑i,PolygonArea.area (imageBank f i))≤∑i,∑c,PolygonArea.area (Q i c) := by
      apply Finset.sum_le_sum
      intro i _
      exact (PolygonArea.area_mono (hbank i)).trans (PolygonArea.area_finset_sup_le _ _)
    _=∑c,PolygonArea.area (P c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp only [Q,apply_ite,PolygonArea.area_bot,PolygonArea.area_translation]
      simp
    _=1 := hsumP

end PolygonPlacement
end PolygonPlacementArea

section PolygonCommonNeighbor

open Classical Set
namespace PolygonPlacement

theorem placement_in_bank {a m : ℕ} (hm : 0 < m) (V : Fin m → polygonAlgebra a)
    (hV : 1 < ∑i,PolygonArea.area (V i)) :
    ∃ e : PolygonPlacement a m,∀x,(e x).2∈(V (e x).1).val := by
  let i₀ : Fin m := ⟨0,hm⟩
  let U : Fin m → polygonAlgebra a := fun i => if i=i₀ then ⊤ else ⊥
  have hU : (∑i,PolygonArea.area (U i))=1 := by
    simp [U,apply_ite,PolygonArea.area_bot,PolygonArea.area_top]
  obtain ⟨f,hf⟩ := PolygonGrid.strict_comparison U V (by rwa [hU])
  let PU : PolygonObject a := ⟨m,U⟩
  let PV : PolygonObject a := ⟨m,V⟩
  let src (x : GenericSquare a) : PU.Point := ⟨(i₀,x),by simp [PU,U]⟩
  let ef : GenericSquare a ↪ TrackPoint a m :=
    ⟨fun x => (f (src x)).val,fun x y he =>
      congrArg (fun p : PU.Point => p.val.2) (f.injective (Subtype.ext he))⟩
  have hetab : ∃s : Finset (Fin m × (CutRing×CutRing) × polygonAlgebra a),
      (∀c∈s,∀x∈c.2.2.val,ef x=(c.1,translate a c.2.1 x)) ∧
      ∀x,∃c∈s,x∈c.2.2.val := by
    obtain ⟨s,hs,hcover⟩ := hf
    let t := s.filter (fun c => c.source=i₀)
    let conv : PolygonObject.Chart (a:=a) m m → Fin m × (CutRing×CutRing) × polygonAlgebra a :=
      fun c => (c.target,c.shift,c.domain)
    refine ⟨t.image conv,?_,?_⟩
    · intro c hc
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hds,hdsrc⟩ := Finset.mem_filter.mp hd
      intro x hx
      obtain ⟨hu,he⟩ := hs d hds x hx
      change (f (src x)).val=(d.target,translate a d.shift x)
      simpa only [src,hdsrc] using he
    · intro x
      obtain ⟨c,hc,hx⟩ := hcover (src x)
      refine ⟨conv c,Finset.mem_image.mpr ⟨c,?_,rfl⟩,hx.2⟩
      exact Finset.mem_filter.mpr ⟨hc,hx.1.symm⟩
  exact ⟨⟨ef,hetab⟩,fun x => (f (src x)).property⟩

theorem common_neighbor {a m : ℕ} (S : Finset (PolygonPlacement a m))
    (hm : S.card+1 < m) : ∃e : PolygonPlacement a m,∀f∈S,Apart e f := by
  let B (i : Fin m) : polygonAlgebra a := S.sup (fun f => imageBank f i)
  let V (i : Fin m) : polygonAlgebra a := (B i)ᶜ
  have hB : (∑i,PolygonArea.area (B i))≤S.card := by
    calc
      _≤∑i,∑f∈S,PolygonArea.area (imageBank f i) :=
        Finset.sum_le_sum (fun i _ => PolygonArea.area_finset_sup_le S _)
      _=∑f∈S,∑i,PolygonArea.area (imageBank f i) := Finset.sum_comm
      _≤∑_∈S,(1:ENNReal) := Finset.sum_le_sum (fun f _ => imageBank_area_le f)
      _=S.card := by simp
  have hsum : (∑i,PolygonArea.area (B i))+(∑i,PolygonArea.area (V i))=m := by
    rw [←Finset.sum_add_distrib]
    simp only [V,PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hV : 1 < ∑i,PolygonArea.area (V i) := by
    by_contra hn
    have hh : (m:ENNReal)≤S.card+1 :=
      hsum.symm.trans_le (add_le_add hB (le_of_not_gt hn))
    have hml : (S.card:ENNReal)+1 < m := by exact_mod_cast hm
    exact (not_le_of_gt hml) hh
  obtain ⟨e,he⟩ := placement_in_bank (by omega : 0 < m) V hV
  refine ⟨e,fun f hf => ?_⟩
  rw [apart_iff]
  intro x y hxy
  have hn := he x
  change (e x).2∉(B (e x).1).val at hn
  apply hn
  have hin : (imageBank f (e x).1).val⊆(B (e x).1).val := by
    change imageBank f (e x).1 ≤ S.sup (fun g => imageBank g (e x).1)
    exact Finset.le_sup (f := fun g : PolygonPlacement a m => imageBank g (e x).1) hf
  apply hin
  refine ⟨y,?_⟩
  exact hxy.symm

theorem configuration_lowDegree_exact {a m n : ℕ} (hm : 33 ≤ m) (hn : n ≤ 2) :
    Function.Exact (ConfigurationChains.degreeBoundary (@Apart a m) (n+1))
      (ConfigurationChains.degreeBoundary (@Apart a m) n) := by
  apply ConfigurationChains.lowDegree_exact _ hn
  intro S hS
  exact common_neighbor S (by omega)

end PolygonPlacement
end PolygonCommonNeighbor

end SimpleAmenable
end
end

end OAI
