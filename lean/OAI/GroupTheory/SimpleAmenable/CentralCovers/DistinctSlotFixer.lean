import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PrivateBankWord
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.PrivateBankReserve
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrivateBankFixer

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section DistinctSlotFixer
namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

theorem distinct_slot_fixer (ι : Fin 5 ↪ Fin (m+1))
    (b : Fin (m+1)) (hb : b ∉ orderedTrackAlphabet ι)
    (u : Fin (m+1) → CutRing × CutRing)
    (F : OffsetFrame a r m hm (orderedTrackAlphabet ι) u)
    (V : polygonAlgebra a) (J : Finset (Fin (m+1)))
    (hreserve : 20 ≤ ((Finset.univ : Finset (Fin (m+1))) \ (insert b J ∪ orderedTrackAlphabet ι)).card)
    (z : BoundedRelationCover M (alternatingGenerator a r m hm))
    (hz : z ∈ ⨆ W : polygonAlgebra a, (B.polygonStar hlarge h hr W).range)
    (hzJ : z ∈ sourceAlignedGroup a r m hm M B.t J)
    (hfix : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (ι i,translate a (u (ι i)) x.val) =
        (ι i,translate a (u (ι i)) x.val))
    (s : UniversalExtension (alternatingGroup (Fin 5))) :
    Commute z (B.distinctSlotStar hlarge h hr ι u F V s) := by
  classical
  obtain ⟨e,he,hprivate⟩ := exists_private_bank ι (insert b J) hreserve
  have heq : bankColumn e 0=ι := Function.Embedding.ext he
  have hb' : b ∉ bankAlphabet e := by
    intro hii
    obtain ⟨⟨i,j⟩,_,hij⟩ := Finset.mem_map.mp hii
    by_cases hj : j=0
    · subst j
      rw [he i] at hij
      exact hb (hij ▸ orderedTrackAlphabet_mem ι i)
    · exact hprivate i j hj (hij.symm ▸ Finset.mem_insert_self b J)
  let v : Fin 5 → CutRing × CutRing := fun i => u (ι i)
  let u' : Fin (m+1) → CutRing × CutRing := Function.extend e (fun p => v p.1) (fun _ => 0)
  have hu : ∀ i j, u' (e (i,j))=v i := fun i j => e.injective.extend_apply _ _ (i,j)
  let G := balancedOffsetFrame a r m hm (bankAlphabet e) b hb' u'
  have hfix' : ∀ (i : Fin 5) (x : V.val),
      (coverMap M (alternatingGenerator a r m hm) z).val.val (e (i,0),translate a (u' (e (i,0))) x.val) =
        (e (i,0),translate a (u' (e (i,0))) x.val) := by
    intro i x
    rw [hu i 0,he i]
    exact hfix i x
  have hh := B.private_bank_source_fixer hlarge h hr e b hb' u' v hu G V J
    (fun i j hj hjJ => hprivate i j hj (Finset.mem_insert_of_mem hjJ)) z hz hzJ hfix' s
  let G0 : OffsetFrame a r m hm (orderedTrackAlphabet ι) u' := heq ▸ G.restrict (bankColumn_subset e 0)
  have huv : ∀ k ∈ orderedTrackAlphabet ι, u k=u' k := by
    intro k hk
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hk
    rw [← he i,hu i 0]
    exact congrArg u (he i)
  have hehom : B.distinctSlotStar hlarge h hr ι u F V =
      B.distinctSlotStar hlarge h hr ι u' G0 V := by
    unfold distinctSlotStar
    rw [B.frameStar_independent hlarge h hr (orderedTrackAlphabet ι)
      (by rw [orderedTrackAlphabet,Finset.card_map,Finset.card_univ,Fintype.card_fin])
      b hb u u' F G0 huv V]
  rw [hehom]
  subst ι
  exact hh

end InitialCoverSystem
end DistinctSlotFixer

end SimpleAmenable
end
end

end OAI
