import Mathlib
import OAI.Geometry.HyperbolicGroups.FanApex

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.FanLink
open Equiv
namespace Mark
variable {F G : Type*}
def map (e : F ≃ G) : Mark F → Mark G
  | absent => absent
  | triangle => triangle
  | top f => top (e f)
@[simp] lemma map_absent (e : F ≃ G) (m : Mark F) : map e m = absent ↔ m = absent := by cases m <;> simp [map]
@[simp] lemma map_triangle (e : F ≃ G) (m : Mark F) : map e m = triangle ↔ m = triangle := by cases m <;> simp [map]
@[simp] lemma map_top (e : F ≃ G) (m : Mark F) (g : G) : map e m = top g ↔ m = top (e.symm g) := by
  cases m <;> simp [map,Equiv.eq_symm_apply]
end Mark

/-- The same local finite-link data, with natural geometric index types.
`toFin` is only a change of finite coordinates, not an additional assumption. -/
structure IndexedFanData (I F O : Type*) (L : I → Type*) [Fintype I] [Fintype F] [Fintype O]
    [∀ z, Fintype (L z)] where
  next : (z : I) → Equiv.Perm (L z)
  cyclic : ∀ z, IsCyclic (next z)
  mark : (z : I) → L z → Mark F
  line : (z : I) → L z → Bool
  occurrence : F → O
  represented : ∀ z, ∃ i, mark z i ≠ .absent
  card_le : ∀ z, Fintype.card (L z) ≤ 5
  no_fixed : ∀ z i, next z i ≠ i
  bipartite : ∀ z i, mark z i = .triangle → line z i ≠ line z (next z i)
  no_backtrack : ∀ z i, mark z i = .triangle → mark z (next z i) = .triangle → next z (next z i) ≠ i
  no_same_side : ∀ z i f g, mark z i = .top f → mark z (next z i) = .top g → occurrence f ≠ occurrence g
  unique_turn : ∀ (p q : Σ z, L z) f, mark p.1 p.2 = .top f → mark q.1 q.2 = .top f → p = q

namespace IndexedFanData
variable {I F O : Type*} {L : I → Type*} [Fintype I] [Fintype F] [Fintype O]
  [∀ z, Fintype (L z)] (D : IndexedFanData I F O L)

def numberLink (_D : IndexedFanData I F O L) (z : Fin (Fintype.card I)) : ℕ := Fintype.card (L ((Fintype.equivFin I).symm z))

def linkEquiv (z : Fin (Fintype.card I)) :
    L ((Fintype.equivFin I).symm z) ≃ Fin (D.numberLink z) := Fintype.equivFin _

def nextFin (z : Fin (Fintype.card I)) : Equiv.Perm (Fin (D.numberLink z)) :=
  (D.linkEquiv z).permCongr (D.next ((Fintype.equivFin I).symm z))

lemma nextFin_symm (z : Fin (Fintype.card I)) (i : Fin (D.numberLink z)) :
    (D.linkEquiv z).symm (D.nextFin z i) =
      D.next ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i) := by
  simp [nextFin,Equiv.permCongr_apply]

lemma nextFin_cyclic (z : Fin (Fintype.card I)) : IsCyclic (D.nextFin z) := by
  intro i j
  obtain ⟨k,hk⟩ := D.cyclic ((Fintype.equivFin I).symm z)
    ((D.linkEquiv z).symm i) ((D.linkEquiv z).symm j)
  refine ⟨k,?_⟩
  have he : D.nextFin z ^ k = (D.linkEquiv z).permCongr
      (D.next ((Fintype.equivFin I).symm z) ^ k) :=
    (map_pow (D.linkEquiv z).permCongrHom _ _).symm
  rw [he,Equiv.permCongr_apply,hk,Equiv.apply_symm_apply]

def markFin (z : Fin (Fintype.card I)) (i : Fin (D.numberLink z)) : Mark (Fin (Fintype.card F)) :=
  Mark.map (Fintype.equivFin F) (D.mark ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i))

def decode : (Σ z, Fin (D.numberLink z)) → Σ z, L z := fun p =>
  ⟨(Fintype.equivFin I).symm p.1,(D.linkEquiv p.1).symm p.2⟩

lemma decode_injective : Function.Injective D.decode := by
  intro p q h
  have hz : p.1 = q.1 := (Fintype.equivFin I).symm.injective (congrArg Sigma.fst h)
  rcases p with ⟨z,i⟩; rcases q with ⟨y,j⟩
  dsimp at hz
  subst y
  have h' := Sigma.mk.inj h
  have hij : i = j := (D.linkEquiv z).symm.injective (eq_of_heq h'.2)
  subst j
  rfl

/-- Transport to the already proved finite-coordinate fan inequality. -/
def toFin : FanData (Fintype.card I) (Fintype.card F) (Fintype.card O) where
  n := D.numberLink
  next := D.nextFin
  cyclic := D.nextFin_cyclic
  mark := D.markFin
  line := fun z i => D.line ((Fintype.equivFin I).symm z) ((D.linkEquiv z).symm i)
  occurrence := fun f => Fintype.equivFin O (D.occurrence ((Fintype.equivFin F).symm f))
  represented := by
    intro z
    obtain ⟨x,hx⟩ := D.represented ((Fintype.equivFin I).symm z)
    refine ⟨D.linkEquiv z x,?_⟩
    simpa only [markFin,ne_eq,Mark.map_absent,Equiv.symm_apply_apply] using hx
  card_le := fun z => D.card_le _
  no_fixed := by
    intro z i h
    have hh := congrArg (D.linkEquiv z).symm h
    rw [D.nextFin_symm] at hh
    exact D.no_fixed _ _ hh
  bipartite := by
    intro z i h
    simp only [markFin,Mark.map_triangle] at h
    simpa only [D.nextFin_symm] using D.bipartite _ _ h
  no_backtrack := by
    intro z i hi hj he
    simp only [markFin,Mark.map_triangle,D.nextFin_symm] at hi hj
    have hh := congrArg (D.linkEquiv z).symm he
    simp only [D.nextFin_symm] at hh
    exact D.no_backtrack _ _ hi hj hh
  no_same_side := by
    intro z i f g hf hg he
    simp only [markFin,Mark.map_top,D.nextFin_symm] at hf hg
    exact D.no_same_side _ _ _ _ hf hg ((Fintype.equivFin O).injective he)
  unique_turn := by
    intro p q f hp hq
    simp only [markFin,Mark.map_top] at hp hq
    exact D.decode_injective (D.unique_turn (D.decode p) (D.decode q) _ hp hq)

end IndexedFanData
end HyperbolicObstruction.FanLink
end
end

section

end
end

end OAI
