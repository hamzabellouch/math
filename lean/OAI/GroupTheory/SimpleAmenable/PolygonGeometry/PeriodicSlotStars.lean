import Mathlib
import OAI.GroupTheory.SimpleAmenable.CentralCovers.CanonicalSlotStars
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.RoutingIndependence

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement

noncomputable def orbitRepresentative (u : CutRing × CutRing) : CutRing × CutRing :=
  ((u.1.im : CutRing)*cutTau,(u.2.im : CutRing)*cutTau)

theorem translate_orbitRepresentative (a : ℕ) (u : CutRing × CutRing) (x : GenericSquare a) :
    translate a u x=translate a (orbitRepresentative u) x :=
  congrArg (fun e : Equiv.Perm (GenericSquare a) => e x) (translation_reduce a u)

theorem cut_im_eq_of_fract_eq (x : ℝ) (u v : CutRing)
    (he : Int.fract (x+ordinary u)=Int.fract (x+ordinary v)) : u.im=v.im := by
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp he
  have huv : u-v=(n : CutRing) := by
    apply ordinary_injective
    simp only [map_sub,map_intCast]
    linarith
  have him : u.im-v.im=0 := by simpa using congrArg (fun z : CutRing => z.im) huv
  omega

theorem orbitRepresentative_eq_of_translate_eq {a : ℕ} {u v : CutRing × CutRing}
    (x : GenericSquare a) (he : translate a u x=translate a v x) :
    orbitRepresentative u=orbitRepresentative v := by
  have hx := congrArg (fun p : GenericSquare a => p.val.1) he
  have hy := congrArg (fun p : GenericSquare a => p.val.2) he
  have hu := cut_im_eq_of_fract_eq x.val.1 u.1 v.1 hx
  have hv := cut_im_eq_of_fract_eq x.val.2 u.2 v.2 hy
  simp only [orbitRepresentative,hu,hv]

theorem SlotMap_orbitRepresentative {a m : ℕ} (V : polygonAlgebra a)
    (i : Fin 5 → Fin m) (u : Fin 5 → CutRing × CutRing) :
    SlotMap a m V (fun j => (i j,u j))=
      SlotMap a m V (fun j => (i j,orbitRepresentative (u j))) := by
  funext p
  exact congrArg (fun z => (i p.1,z)) (translate_orbitRepresentative a (u p.1) p.2.val)

noncomputable def OffsetFrame.reduce {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    {I : Finset (Fin (m+1))} {u : Fin (m+1) → CutRing × CutRing}
    (F : OffsetFrame a r m hm I u) :
    OffsetFrame a r m hm I (fun t => orbitRepresentative (u t)) where
  k := F.k
  d := fun t => orbitRepresentative (F.d t)
  projection := F.projection.trans (trackTranslation_reduce _)
  prescribed := fun t ht => congrArg orbitRepresentative (F.prescribed t ht)

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws) (hr : 0<ordinary r ∧ ordinary r<1/2)

namespace SlotRouting
variable {B hlarge h hr}

noncomputable def reduce {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u) :
    B.SlotRouting hlarge h hr V i (fun j => orbitRepresentative (u j)) where
  alphabet := ρ.alphabet
  card_le := ρ.card_le
  source_mem := ρ.source_mem
  target := ρ.target
  target_mem := ρ.target_mem
  offsets := fun t => orbitRepresentative (ρ.offsets t)
  offsets_spec := fun j => congrArg orbitRepresentative (ρ.offsets_spec j)
  frame := ρ.frame.reduce
  word := ρ.word
  aligned := ρ.aligned
  supported := ρ.supported
  transport := by
    intro j x
    rw [← translate_orbitRepresentative a (u j)]
    exact ρ.transport j x

theorem reduce_star {V : polygonAlgebra a} {i : Fin 5 → Fin (m+1)}
    {u : Fin 5 → CutRing × CutRing} (ρ : B.SlotRouting hlarge h hr V i u) :
    ρ.reduce.star=ρ.star := rfl

theorem star_empty {i : Fin 5 → Fin (m+1)} {u : Fin 5 → CutRing × CutRing}
    (ρ : B.SlotRouting hlarge h hr ⊥ i u) : ρ.star=1 := by
  ext s : 1
  change ρ.word⁻¹*B.frameStar hlarge h hr (orderedTrackAlphabet ρ.target) ρ.offsets ρ.frame ⊥
    (universalMap (orderedTrackHom ρ.target) s)*(ρ.word⁻¹)⁻¹=1
  rw [B.frameStar_empty hlarge h hr]
  simp

end SlotRouting

variable (R : alternatingGroup (Fin (m+1)) →
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)) →*
      Multiplicative (FreeAbelianGroup (Fin m × Fin 2)))
    (hR : ∀ s k, B.c s * B.t k * (B.c s)⁻¹ = B.t (R s k))
    (hwide : 100 ≤ m+1)

include R hR

theorem slotStar_reduce (V : polygonAlgebra a) (i : Fin 5 → Fin (m+1))
    (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j)))) :
    B.slotStar hlarge h hr hwide V i u hinj=
      B.slotStar hlarge h hr hwide V i (fun j => orbitRepresentative (u j))
        (by rw [← SlotMap_orbitRepresentative]; exact hinj) := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) V i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide V i u hinj ρ,
    B.slotStar_eq_routing hlarge h hr R hR hwide V i _ _ ρ.reduce,ρ.reduce_star]

theorem slotStar_empty (i : Fin 5 → Fin (m+1)) (u : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) (⊥ : polygonAlgebra a) (fun j => (i j,u j)))) :
    B.slotStar hlarge h hr hwide ⊥ i u hinj=1 := by
  let ρ := (B.slotRouting_nonempty hlarge h hr (by omega) ⊥ i u hinj).some
  rw [B.slotStar_eq_routing hlarge h hr R hR hwide ⊥ i u hinj ρ,ρ.star_empty]

theorem slotStar_parameterwise (V : polygonAlgebra a)
    (i k : Fin 5 → Fin (m+1)) (u v : Fin 5 → CutRing × CutRing)
    (hinj : Function.Injective (SlotMap a (m+1) V (fun j => (i j,u j))))
    (hkinj : Function.Injective (SlotMap a (m+1) V (fun j => (k j,v j))))
    (he : ∀ j, ∀ x : V.val, (i j,translate a (u j) x.val)=(k j,translate a (v j) x.val)) :
    B.slotStar hlarge h hr hwide V i u hinj=B.slotStar hlarge h hr hwide V k v hkinj := by
  by_cases hV : V.val.Nonempty
  · obtain ⟨x,hx⟩ := hV
    have hik : i=k := funext (fun j => congrArg Prod.fst (he j ⟨x,hx⟩))
    have huv : (fun j => orbitRepresentative (u j))=(fun j => orbitRepresentative (v j)) := by
      funext j
      exact orbitRepresentative_eq_of_translate_eq x (congrArg Prod.snd (he j ⟨x,hx⟩))
    rw [B.slotStar_reduce hlarge h hr R hR hwide V i u hinj,
      B.slotStar_reduce hlarge h hr R hR hwide V k v hkinj]
    congr 1
  · have hbot : V=⊥ := Subtype.ext (Set.not_nonempty_iff_eq_empty.mp hV)
    subst V
    rw [B.slotStar_empty hlarge h hr R hR hwide,B.slotStar_empty hlarge h hr R hR hwide]

end InitialCoverSystem

end SimpleAmenable

end OAI
