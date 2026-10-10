import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonPiecewiseSlots

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonBankEmbedding

open Classical Set
namespace PolygonObject

structure BankEmbedding {a : ℕ} (U : PolygonObject a) (m : ℕ) where
  emb : U.Point ↪ TrackPoint a m
  table : HasTable (fun x => (⟨emb x,by trivial⟩ : (whole a m).Point))

namespace BankEmbedding
variable {a m : ℕ} {U : PolygonObject a}
instance : CoeFun (BankEmbedding U m) (fun _ => U.Point → TrackPoint a m) := ⟨fun f => f.emb⟩

theorem injective (f : BankEmbedding U m) : Function.Injective f := f.emb.injective

theorem range_fiber_polygon (f : BankEmbedding U m) (i : Fin m) :
    {x | (i,x)∈Set.range f}∈polygonAlgebra a := by
  obtain ⟨S,hS,hcov⟩ := f.table
  change Finset (Chart (a:=a) U.tracks m) at S
  let Q (c : Chart (a:=a) U.tracks m) : polygonAlgebra a :=
    if c.target=i then translatedPolygon c.shift c.domain else ⊥
  have he : {x | (i,x)∈Set.range f}=(S.sup Q).val := by
    rw [PolygonArea.val_finset_sup]
    ext y
    constructor
    · rintro ⟨p,hp⟩
      obtain ⟨c,hc,hs,hx⟩ := hcov p
      obtain ⟨hu,hf⟩ := hS c hc p.val.2 hx
      have he : (⟨(c.source,p.val.2),hu⟩ : U.Point)=p := Subtype.ext (Prod.ext hs.symm rfl)
      change f ⟨(c.source,p.val.2),hu⟩=(c.target,translate a c.shift p.val.2) at hf
      rw [he,hp] at hf
      refine Set.mem_iUnion₂.mpr ⟨c,hc,?_⟩
      have ht : c.target=i := (congrArg Prod.fst hf).symm
      simp only [Q,ht,ite_true]
      exact ⟨p.val.2,hx,(congrArg Prod.snd hf).symm⟩
    · intro hy
      obtain ⟨c,hc,hy⟩ := Set.mem_iUnion₂.mp hy
      by_cases ht : c.target=i
      · simp only [Q,ht,ite_true] at hy
        obtain ⟨x,hx,rfl⟩ := hy
        obtain ⟨hu,he⟩ := hS c hc x hx
        refine ⟨⟨(c.source,x),hu⟩,?_⟩
        change f ⟨(c.source,x),hu⟩=(c.target,translate a c.shift x) at he
        change f ⟨(c.source,x),hu⟩=(i,translate a c.shift x)
        exact he.trans (congrArg (fun j => (j,translate a c.shift x)) ht)
      · simp only [Q,ht,ite_false] at hy
        exact False.elim hy
  rw [he]
  exact (S.sup Q).property

noncomputable def imageBank (f : BankEmbedding U m) (i : Fin m) : polygonAlgebra a :=
  ⟨{x | (i,x)∈Set.range f},range_fiber_polygon f i⟩

theorem imageBank_area_le (f : BankEmbedding U m) :
    (∑i,PolygonArea.area (imageBank f i))≤∑r,PolygonArea.area (U.cell r) := by
  obtain ⟨S,hS,hcov⟩ := f.table
  change Finset (Chart (a:=a) U.tracks m) at S
  let D (r : Fin U.tracks) (c : S) : polygonAlgebra a :=
    if c.val.source=r then c.val.domain else ⊥
  have hD (r : Fin U.tracks) (c : S) (x : GenericSquare a) :
      x∈(D r c).val ↔ c.val.source=r ∧ x∈c.val.domain.val := by
    by_cases h : c.val.source=r <;> simp [D,h]
  have hd_sub (r : Fin U.tracks) (c : S) : D r c≤U.cell r := by
    intro x hx
    obtain ⟨hr,hx⟩ := (hD r c x).mp hx
    have hu := (hS c.val c.property x hx).1
    simpa only [hr] using hu
  have hd_cover (r : Fin U.tracks) (x : GenericSquare a) (hx : x∈(U.cell r).val) :
      ∃c : S,x∈(D r c).val := by
    obtain ⟨c,hc,hr,hd⟩ := hcov ⟨(r,x),hx⟩
    exact ⟨⟨c,hc⟩,(hD r ⟨c,hc⟩ x).mpr ⟨hr.symm,hd⟩⟩
  have ex (r : Fin U.tracks) := Fintype.exists_disjointed_le (D r)
  choose P hP hSup hdisP using ex
  have hcoverP (r : Fin U.tracks) : (U.cell r).val=⋃c,(P r c).val := by
    have hv := congrArg (fun A : polygonAlgebra a => A.val) (hSup r)
    simp only [PolygonArea.val_finset_sup,Finset.mem_univ,Set.iUnion_true] at hv
    rw [hv]
    ext x
    exact ⟨fun hx => Set.mem_iUnion.mpr (hd_cover r x hx),fun hx =>
      by obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx;exact hd_sub r c hc⟩
  have hsumP (r : Fin U.tracks) : (∑c,PolygonArea.area (P r c))=PolygonArea.area (U.cell r) := by
    symm
    apply PolygonArea.area_eq_sum _ (P r) (hcoverP r)
    intro c d hcd
    have h : Disjoint (P r c) (P r d) := hdisP r hcd
    rw [disjoint_iff] at h
    exact Set.disjoint_iff_inter_eq_empty.mpr (congrArg (fun A : polygonAlgebra a => A.val) h)
  let Q (i : Fin m) (r : Fin U.tracks) (c : S) : polygonAlgebra a :=
    if c.val.target=i then translatedPolygon c.val.shift (P r c) else ⊥
  have hbank (i : Fin m) : imageBank f i≤Finset.univ.sup (fun r => Finset.univ.sup (Q i r)) := by
    intro y hy
    obtain ⟨p,hpy⟩ := hy
    have hx : p.val.2∈⋃c,(P p.val.1 c).val := by rw [←hcoverP];exact p.property
    obtain ⟨c,hc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hr,hd⟩ := (hD p.val.1 c p.val.2).mp (hP p.val.1 c hc)
    obtain ⟨hu,he⟩ := hS c.val c.property p.val.2 hd
    have he' : (⟨(c.val.source,p.val.2),hu⟩ : U.Point)=p := Subtype.ext (Prod.ext hr rfl)
    change f ⟨(c.val.source,p.val.2),hu⟩=(c.val.target,translate a c.val.shift p.val.2) at he
    rw [he',hpy] at he
    simp only [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨p.val.1,Finset.mem_univ _,Set.mem_iUnion₂.mpr ⟨c,Finset.mem_univ _,?_⟩⟩
    have ht : c.val.target=i := (congrArg Prod.fst he).symm
    simp only [Q,ht,ite_true]
    exact ⟨p.val.2,hc,(congrArg Prod.snd he).symm⟩
  calc
    (∑i,PolygonArea.area (imageBank f i)) ≤ ∑i,∑r,∑c,PolygonArea.area (Q i r c) := by
      apply Finset.sum_le_sum
      intro i _
      exact (PolygonArea.area_mono (hbank i)).trans ((PolygonArea.area_finset_sup_le _ _).trans
        (Finset.sum_le_sum (fun r _ => PolygonArea.area_finset_sup_le _ _)))
    _ = ∑r,∑c,PolygonArea.area (P r c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp [Q,apply_ite,PolygonArea.area_bot,PolygonArea.area_translation]
    _ = ∑r,PolygonArea.area (U.cell r) := Finset.sum_congr rfl (fun r _ => hsumP r)

theorem exists_into {U V : Fin m → polygonAlgebra a}
    (h : (∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (V i)) :
    ∃f : BankEmbedding (PolygonObject.mk m U) m,∀p,(f p).2∈(V (f p).1).val := by
  obtain ⟨f,hf⟩ := PolygonGrid.strict_comparison U V h
  exact ⟨⟨⟨fun p => (f p).val,fun _ _ he => f.injective (Subtype.ext he)⟩,hf⟩,fun p => (f p).property⟩

end BankEmbedding
end PolygonObject
end PolygonBankEmbedding

section PolygonBankReserve

open Classical Set
namespace PolygonObject
namespace BankEmbedding
variable {a m b : ℕ}

noncomputable def inclusion (U : Fin m → polygonAlgebra a) : BankEmbedding (PolygonObject.mk m U) m :=
  ⟨⟨Subtype.val,Subtype.val_injective⟩,intoWhole_hasTable (identity_hasTable _)⟩

theorem exists_away (U B : Fin m → polygonAlgebra a)
    (f : Fin b → BankEmbedding (PolygonObject.mk m U) m)
    (h : (∑i,PolygonArea.area (B i))+(b+1:ENNReal)*(∑i,PolygonArea.area (U i)) < m) :
    ∃g : BankEmbedding (PolygonObject.mk m U) m,
      (∀p,(g p).2∉(B (g p).1).val) ∧ ∀j p q,g p≠f j q := by
  let D (i : Fin m) : polygonAlgebra a :=
    B i ⊔ Finset.univ.sup (fun j => imageBank (f j) i)
  let V (i : Fin m) : polygonAlgebra a := (D i)ᶜ
  have hD : (∑i,PolygonArea.area (D i))≤
      (∑i,PolygonArea.area (B i))+(b:ENNReal)*(∑i,PolygonArea.area (U i)) := by
    calc
      _≤∑i,(PolygonArea.area (B i)+∑j,PolygonArea.area (imageBank (f j) i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (PolygonArea.area_sup_le _ _).trans (add_le_add le_rfl (PolygonArea.area_finset_sup_le _ _))
      _=(∑i,PolygonArea.area (B i))+∑j,∑i,PolygonArea.area (imageBank (f j) i) := by
        rw [Finset.sum_add_distrib,Finset.sum_comm]
      _≤(∑i,PolygonArea.area (B i))+∑_j : Fin b,∑i,PolygonArea.area (U i) :=
        add_le_add le_rfl (Finset.sum_le_sum (fun j _ => imageBank_area_le (f j)))
      _=_ := by simp
  have hDV : (∑i,PolygonArea.area (D i))+(∑i,PolygonArea.area (V i))=m := by
    rw [←Finset.sum_add_distrib]
    simp only [V,PolygonArea.area_compl,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hV : (∑i,PolygonArea.area (U i))<∑i,PolygonArea.area (V i) := by
    by_contra hn
    have hh := (add_le_add hD (le_of_not_gt hn))
    rw [hDV] at hh
    have he : (∑i,PolygonArea.area (B i))+(b:ENNReal)*(∑i,PolygonArea.area (U i))+
        (∑i,PolygonArea.area (U i)) =
        (∑i,PolygonArea.area (B i))+(b+1:ENNReal)*(∑i,PolygonArea.area (U i)) := by
      rw [add_mul,one_mul,add_assoc]
    rw [he] at hh
    exact (not_le_of_gt h) hh
  obtain ⟨g,hg⟩ := exists_into hV
  refine ⟨g,?_,?_⟩
  · intro p hB
    exact hg p (Or.inl hB)
  · intro j p q he
    apply hg p
    right
    rw [PolygonArea.val_finset_sup]
    refine Set.mem_iUnion₂.mpr ⟨j,Finset.mem_univ _,?_⟩
    exact ⟨q,he.symm⟩

theorem cycle_three {U : PolygonObject a} (f g h : BankEmbedding U m)
    (hfg : ∀p q,f p≠g q) (hfh : ∀p q,f p≠h q) (hgh : ∀p q,g p≠h q) :
    ∃ c : polygonAlternatingGroup a m,
      (∀p,c.val.val (f p)=g p) ∧
      (∀y,(∀p,f p≠y) → (∀p,g p≠y) → (∀p,h p≠y) → c.val.val y=y) := by
  let slots : Fin 3 → BankEmbedding U m := ![f,g,h]
  have hinj : Function.Injective (fun p : Fin 3 × U.Point => slots p.1 p.2) := by
    rintro ⟨i,p⟩ ⟨j,q⟩ he
    have hij : i=j := by
      fin_cases i <;> fin_cases j <;> simp only [slots] at he ⊢
      · exact False.elim (hfg p q he)
      · exact False.elim (hfh p q he)
      · exact False.elim (hfg q p he.symm)
      · exact False.elim (hgh p q he)
      · exact False.elim (hfh q p he.symm)
      · exact False.elim (hgh q p he.symm)
    subst j
    exact Prod.ext rfl ((slots i).injective he)
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hσ : σ∈alternatingGroup (Fin 3) := by
    simp [σ,Equiv.Perm.mem_alternatingGroup,Equiv.Perm.sign_mul]
  obtain ⟨c,hc,hout⟩ := PolygonPiecewise.even_slots U (fun i => slots i) hinj (fun i => (slots i).table) σ hσ
  refine ⟨c,?_,?_⟩
  · intro p
    have hz : σ 0=1 := by decide
    have hu := hc 0 p
    rw [hz] at hu
    exact hu
  · intro y hyf hyg hyh
    apply hout y
    rintro ⟨⟨i,p⟩,he⟩
    fin_cases i
    · exact hyf p he
    · exact hyg p he
    · exact hyh p he

end BankEmbedding
end PolygonObject
end PolygonBankReserve

end SimpleAmenable
end
end

end OAI
