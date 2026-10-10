import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TransitiveInduction
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PolygonBankEmbedding

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAlternatingConfigurations

open Classical CategoryTheory Set
namespace PolygonPlacement
variable {a m n : ℕ}

noncomputable def bankEmbedding (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j))) :
    PolygonObject.BankEmbedding (PolygonObject.whole a n) m where
  emb := ⟨fun x => bank f hf x.val,fun x y h => Subtype.ext ((bank f hf).injective h)⟩
  table := by
    choose S hS hcov using fun i => (f i).charts
    let c (i : Fin n) (k : Fin m × (CutRing×CutRing) × polygonAlgebra a) :
        PolygonObject.Chart (a:=a) n m := ⟨i,k.1,k.2.1,k.2.2⟩
    refine ⟨Finset.univ.biUnion (fun i => (S i).image (c i)),?_,?_⟩
    · intro k hk
      obtain ⟨i,_,hk⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hk
      intro z hz
      exact ⟨by trivial,hS i d hd z hz⟩
    · intro x
      obtain ⟨d,hd,hz⟩ := hcov x.val.1 x.val.2
      exact ⟨c x.val.1 d,Finset.mem_biUnion.mpr ⟨x.val.1,Finset.mem_univ _,
        Finset.mem_image.mpr ⟨d,hd,rfl⟩⟩,rfl,hz⟩

@[simp] theorem bankEmbedding_apply (f : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (x : (PolygonObject.whole a n).Point) : bankEmbedding f hf x=f x.val.1 x.val.2 := rfl

theorem alternating_disjoint_configurations (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j)))
    (hfg : ∀i j,Apart (f i) (g j)) (hm : 3*n+1 < m) :
    ∃c : polygonAlternatingGroup a m,∀i x,c.val.val (f i x)=g i x := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨c,hc,_⟩ := PolygonObject.BankEmbedding.cycle_three
    (bankEmbedding f hf) (bankEmbedding g hg) (bankEmbedding w hw)
    (fun p q => (apart_iff _ _).mp (hfg p.val.1 q.val.1) p.val.2 q.val.2)
    (fun p q => (apart_iff _ _).mp (hwf q.val.1 p.val.1).symm p.val.2 q.val.2)
    (fun p q => (apart_iff _ _).mp (hwg q.val.1 p.val.1).symm p.val.2 q.val.2)
  exact ⟨c,fun i x => hc ⟨(i,x),by trivial⟩⟩

theorem alternating_configuration_transitive_sharp (f g : Fin n → PolygonPlacement a m)
    (hf : Pairwise (fun i j => Apart (f i) (f j)))
    (hg : Pairwise (fun i j => Apart (g i) (g j))) (hm : 3*n+1 < m) :
    ∃c : polygonAlternatingGroup a m,∀i,c.val • f i=g i := by
  let S := Finset.univ.image f ∪ Finset.univ.image g
  have hS : S.card≤2*n := by
    calc
      _≤(Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
      _≤(Finset.univ : Finset (Fin n)).card+(Finset.univ : Finset (Fin n)).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _=2*n := by simp; omega
  obtain ⟨w,hw,hws⟩ := exists_configuration_avoiding S n (by omega)
  have hwf (i j : Fin n) : Apart (w i) (f j) :=
    hws i (f j) (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  have hwg (i j : Fin n) : Apart (w i) (g j) :=
    hws i (g j) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
  obtain ⟨u,hu⟩ := alternating_disjoint_configurations f w hf hw (fun i j => (hwf j i).symm) hm
  obtain ⟨v,hv⟩ := alternating_disjoint_configurations w g hw hg hwg hm
  refine ⟨v*u,fun i => ?_⟩
  apply PolygonPlacement.ext
  intro x
  change v.val.val (u.val.val (f i x))=g i x
  rw [hu,hv]

namespace Configuration

theorem alternating_transitive {p : ℕ} (f g : Configuration a m p) (hm : 3*p+1 < m) :
    ∃c : polygonAlternatingGroup a m,c.val • f=g := by
  obtain ⟨c,hc⟩ := alternating_configuration_transitive_sharp f.val g.val f.property g.property hm
  exact ⟨c,ext hc⟩

theorem alternating_stabilizer_standard (a p n : ℕ) :
    MulAction.stabilizer (polygonAlternatingGroup a (p+n)) (standard a p n)=
      (PolygonTracks.bankFixer a p n).comap (polygonAlternatingGroup a (p+n)).subtype := by
  ext c
  change c.val∈MulAction.stabilizer (polygonFullGroup a (p+n)) (standard a p n) ↔
    c.val∈PolygonTracks.bankFixer a p n
  rw [stabilizer_standard]

noncomputable def alternatingOrbitHomologyIso (a p n : ℕ) (hm : 3*p+1 < p+n) (q : ℕ) :
    groupHomology (Rep.of (TransitiveInduction.permutationRep
      (G:=polygonAlternatingGroup a (p+n)) (X:=Configuration a (p+n) p))) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer (polygonAlternatingGroup a (p+n))
        (standard a p n)) ℤ) q :=
  TransitiveInduction.homologyIso (standard a p n) (fun f => alternating_transitive _ f hm) q

noncomputable def alternatingRepresentationIso (a m p : ℕ) :
    Rep.of (TransitiveInduction.permutationRep
      (G:=polygonAlternatingGroup a m) (X:=Configuration a m p)) ≅
      Rep.of ((configurationRepresentation a m p).comp (polygonAlternatingGroup a m).subtype) :=
  Rep.mkIso
    { toLinearEquiv := chainEquiv a m p
      isIntertwining' := fun g => chainEquiv_intertwines g.val }

noncomputable def alternatingColumnHomologyIso (a p n : ℕ) (hm : 3*p+1 < p+n) (q : ℕ) :
    groupHomology (Rep.of ((configurationRepresentation a (p+n) p).comp
      (polygonAlternatingGroup a (p+n)).subtype)) q ≅
      groupHomology (Rep.trivial ℤ (MulAction.stabilizer (polygonAlternatingGroup a (p+n))
        (standard a p n)) ℤ) q :=
  (groupHomology.functor ℤ _ q).mapIso (alternatingRepresentationIso a (p+n) p).symm ≪≫
    alternatingOrbitHomologyIso a p n hm q

end Configuration
end PolygonPlacement
end PolygonAlternatingConfigurations

end SimpleAmenable

end

end

end OAI
