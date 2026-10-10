import Mathlib
import OAI.Geometry.HyperbolicGroups.PolygonTarget
import OAI.Geometry.HyperbolicGroups.FrozenWalk
import OAI.Geometry.HyperbolicGroups.ProtectedNormal

namespace OAI

section
section


noncomputable section
namespace HyperbolicObstruction.PictureSwitch
open Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
universe u v w z k t r
variable {S : Type v} {C : Type w} {W : Type z} {L : Type k} {V : Type t}
  {A : Type r} [AddCommMonoid A]
namespace WalkCellTarget
variable (T : WalkCellTarget S C W L V A)
variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → L)
  (closed : ∀ i, T.start (word (finRotate ell i)) = T.start (T.rev (word i)))

/-- The outside word is an arbitrary closed edge path, not an attaching word
of a cell of the target. Its second orientation is solely bookkeeping. -/
def exteriorBoundary : PolygonTarget.Boundary Unit L V where
  size := fun _ => ell
  positive := fun _ => hell
  label := fun _ => word
  start := T.start
  rev := T.rev
  inv := T.rev_rev
  closed := fun _ => closed

abbrev ExteriorSide := (T.exteriorBoundary ell hell word closed).Side

/-- Enlarge the indexing types by one protected exterior polygon. Only the
original target's free cone-walk cells may be split. All added side weights
are zero, so the chain is exactly the interior cellular chain. -/
def withExterior : WalkCellTarget (S ⊕ T.ExteriorSide ell hell word closed)
    (C ⊕ Unit) (W ⊕ V) L V A where
  kind := Sum.elim (Sum.inl ∘ T.kind) (fun _ => .inr ())
  free := Sum.elim T.free (fun _ => false)
  front := Sum.elim (Sum.inl ∘ T.front)
    (fun s => .inr (T.start ((T.exteriorBoundary ell hell word closed).sideLabel s)))
  back := Sum.elim (Sum.inl ∘ T.back)
    (fun s => .inr (T.start (T.rev ((T.exteriorBoundary ell hell word closed).sideLabel s))))
  vertex := Sum.elim T.vertex id
  label := Sum.elim T.label (T.exteriorBoundary ell hell word closed).sideLabel
  start := T.start
  rev := T.rev
  rev_rev := T.rev_rev
  front_label := by rintro (s | s); exact T.front_label s; rfl
  back_label := by rintro (s | s); exact T.back_label s; rfl
  opposite := Sum.map T.opposite (T.exteriorBoundary ell hell word closed).opposite
  opposite_kind := by rintro (s | s); exact congrArg Sum.inl (T.opposite_kind s); rfl
  opposite_front := by
    rintro (s | s)
    · exact congrArg Sum.inl (T.opposite_front s)
    · exact congrArg Sum.inr (congrArg T.start ((T.exteriorBoundary ell hell word closed).edge_opposite s))
  opposite_back := by
    rintro (s | s)
    · exact congrArg Sum.inl (T.opposite_back s)
    · dsimp only [Sum.map_inr,Sum.elim_inr]
      rw [(T.exteriorBoundary ell hell word closed).edge_opposite]
      exact congrArg Sum.inr (congrArg T.start (T.rev_rev _))
  opposite_label := by
    rintro (s | s)
    · exact T.opposite_label s
    · exact (T.exteriorBoundary ell hell word closed).edge_opposite s
  loopless := by
    rintro (s | s) h
    · exact Sum.inl_injective.ne (T.loopless s h)
    · cases h
  simple := by
    rintro (s | s) (t | t) h hk hf hb
    · exact congrArg Sum.inl (T.simple s t h (Sum.inl.inj hk) (Sum.inl.inj hf) (Sum.inl.inj hb))
    · cases hk
    · cases h
    · cases h
  weight := Sum.elim T.weight (fun _ => 0)
  opposite_weight := by
    rintro (s | s) h
    · exact T.opposite_weight s h
    · cases h

variable (B : FrozenTarget T)
def exteriorFrozen : FrozenTarget (T.withExterior ell hell word closed) where
  next := Equiv.sumCongr B.next (T.exteriorBoundary ell hell word closed).next
  reverse := Equiv.sumCongr B.reverse (T.exteriorBoundary ell hell word closed).opposite
  reverse_eq := by rintro (s | s); exact congrArg Sum.inl (B.reverse_eq s); rfl
  reverse_sq := by
    apply Equiv.ext
    rintro (s | s)
    · have h := congrArg (fun p : Perm S => p s) B.reverse_sq
      exact congrArg Sum.inl h
    · have h := congrArg (fun p : Perm (T.ExteriorSide ell hell word closed) => p s)
        (T.exteriorBoundary ell hell word closed).opposite_sq
      exact congrArg Sum.inr h
  reverse_next := by
    rintro (s | s)
    · exact congrArg Sum.inl (B.reverse_next s)
    · exact congrArg Sum.inr ((T.exteriorBoundary ell hell word closed).reverse_next s)
  opposite_cycle := by
    let F : S ⊕ T.ExteriorSide ell hell word closed → Quotient (SameCycle.setoid B.next) ⊕ Bool :=
      Sum.elim (Sum.inl ∘ Quotient.mk _) (fun s => .inr s.2.1)
    have hf : ∀ s, F ((Equiv.sumCongr B.next (T.exteriorBoundary ell hell word closed).next) s) = F s := by
      rintro (s | s)
      · exact congrArg Sum.inl (Quotient.sound (SameCycle.rfl (f := B.next) (x := s)).apply_left)
      · rfl
    rintro (s | ⟨a,b,i⟩) h
    · have he := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid B.next) ⊕ Bool))) hf h)
      exact B.opposite_cycle s (Quotient.exact (Sum.inl.inj he))
    · have he := sameCycle_one.mp (semiconj_perm_sameCycle (t := (1 : Perm (Quotient (SameCycle.setoid B.next) ⊕ Bool))) hf h)
      cases b <;> cases (Sum.inr.inj he)
  opposite_weight := by
    rintro (s | s)
    · exact B.opposite_weight s
    · exact add_zero _

/-- Protect precisely the added exterior sides. -/
def isExterior : S ⊕ T.ExteriorSide ell hell word closed → Prop := Sum.elim (fun _ => False) (fun _ => True)

lemma exterior_frozen (s) (hs : T.isExterior ell hell word closed s) :
    (T.withExterior ell hell word closed).free ((T.withExterior ell hell word closed).kind s) = false := by
  rcases s with s | s
  · exact False.elim hs
  · rfl

lemma exterior_unopposed (P : WalkPicture.{u} (T.withExterior ell hell word closed))
    (hp : ∀ x s, P.index x = .inr s → s.2.1 = true) :
    P.Unopposed (T.isExterior ell hell word closed) := by
  intro x y hx he
  cases hxi : P.index x with
  | inl s => rw [hxi] at hx; exact hx
  | inr s =>
    have hs := hp x s hxi
    rw [hxi] at he
    change P.index y = .inr ((T.exteriorBoundary ell hell word closed).opposite s) at he
    have ht := hp y _ he
    change (!s.2.1) = true at ht
    rw [hs] at ht
    cases ht

/-- Normalization with the literal outside word preserved side-for-side. -/
theorem normalize_exterior (P : WalkPicture.{u} (T.withExterior ell hell word closed))
    (hm : P.FrozenMapped (T.exteriorFrozen ell hell word closed B))
    (hp : ∀ x s, P.index x = .inr s → s.2.1 = true)
    (apex : V → Bool)
    (hr : ∀ l, apex (T.start l) = true → apex (T.start (T.rev l)) = false) :
    ∃ Q : WalkPicture.{u} (T.withExterior ell hell word closed),
      Nonempty (P.Preserves (T.isExterior ell hell word closed) Q) ∧
      Q.FrozenMapped (T.exteriorFrozen ell hell word closed B) ∧
      Q.Simple ∧ Q.NoBigon ∧ Q.FullyReduced ∧ Q.RadialInjective apex ∧
      Q.chain = P.chain := by
  exact P.normalize_protected _ hm _ (T.exterior_frozen ell hell word closed)
    (T.exterior_unopposed ell hell word closed P hp) apex (fun s => hr _)

end WalkCellTarget
end HyperbolicObstruction.PictureSwitch
end
end

section

end
end

end OAI
