import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PolygonPlacementAlternating

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section PolygonAlternatingStabilization
open Classical Set
namespace PolygonTracks
variable {a k n : ℕ}

theorem stabilize_threeSlot {g : polygonFullGroup a n} (hg : IsThreeSlotCycle g) :
    IsThreeSlotCycle (stabilize a k n g) := by
  obtain ⟨U,s,hU,hs,hg,hfix⟩ := hg
  let t : Fin 3 → Fin (k+n) × (CutRing × CutRing) := fun i => ((s i).1.natAdd k,(s i).2)
  have ht (x : Fin 3 × U.val) : SlotMap a (k+n) U t x=rightIncl a k n (SlotMap a n U s x) := rfl
  refine ⟨U,t,hU,?_,?_,?_⟩
  · intro x y hxy
    apply hs
    exact rightIncl_injective (by simpa only [ht] using hxy)
  · intro i x
    rw [ht,ht]
    change (stabilize a k n g).val ((SlotMap a n U s (i,x)).1.natAdd k,
      (SlotMap a n U s (i,x)).2)=_
    rw [stabilize_right,hg]
    rfl
  · intro p hp
    obtain ⟨q,rfl⟩ := (join a k n).surjective p
    cases q with
    | inl q => exact stabilize_left g q
    | inr q =>
      rw [join_inr,stabilize_right]
      have hq : q∉Set.range (SlotMap a n U s) := by
        rintro ⟨x,rfl⟩
        exact hp ⟨x,rfl⟩
      rw [hfix q hq]

theorem stabilize_mem_alternating (g : polygonAlternatingGroup a n) :
    stabilize a k n g.val∈polygonAlternatingGroup a (k+n) := by
  have hl : polygonAlternatingGroup a n ≤
      (polygonAlternatingGroup a (k+n)).comap (stabilize a k n) := by
    apply (Subgroup.closure_le _).mpr
    intro f hf
    exact Subgroup.subset_closure (stabilize_threeSlot hf)
  exact hl g.property

noncomputable def stabilizeAlternating (a k n : ℕ) :
    polygonAlternatingGroup a n →* polygonAlternatingGroup a (k+n) :=
  (stabilize a k n).restrict (fun g hg => stabilize_mem_alternating ⟨g,hg⟩)

@[simp] theorem stabilizeAlternating_val (g : polygonAlternatingGroup a n) :
    (stabilizeAlternating a k n g).val=stabilize a k n g.val := rfl

theorem stabilizeAlternating_injective : Function.Injective (stabilizeAlternating a k n) := by
  intro g h he
  apply Subtype.ext
  exact stabilize_injective (congrArg Subtype.val he)

theorem exists_alternating_agrees_right (f : polygonFullGroup a (k+n)) (hm : 6*n+7<k+n) :
    ∃c : polygonAlternatingGroup a (k+n),∀x : TrackPoint a n,
      c.val.val (rightIncl a k n x)=f.val (rightIncl a k n x) := by
  let e : Fin n → PolygonPlacement a (k+n) := fun i => PolygonPlacement.standard (i.natAdd k)
  have he : Pairwise (fun i j => PolygonPlacement.Apart (e i) (e j)) := by
    intro i j hij
    exact PolygonPlacement.standard_apart (fun h => hij (Fin.ext (Nat.add_left_cancel
      (congrArg Fin.val h))))
  have hf : Pairwise (fun i j => PolygonPlacement.Apart (f • e i) (f • e j)) := by
    intro i j hij
    exact (PolygonPlacement.apart_smul_iff f _ _).mpr (he hij)
  obtain ⟨c,hc⟩ := PolygonPlacement.alternating_configuration_transitive e (fun i => f • e i) he hf hm
  refine ⟨c,fun x => ?_⟩
  exact congrArg (fun z : PolygonPlacement a (k+n) => z x.2) (hc x.1)

end PolygonTracks
end PolygonAlternatingStabilization

end SimpleAmenable
end
end

end OAI
