import OAI.Probability.ClassicalON.BondConnectivity

namespace OAI

universe uE uV

noncomputable section
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE}

theorem bondConnected_refl (left right : E → V) (η : E → Bool) (x : V) :
    bondConnected left right η x x := fun _ _ => rfl

theorem bondConnected_symm (left right : E → V) (η : E → Bool) {x y : V}
    (h : bondConnected left right η x y) : bondConnected left right η y x := fun s hs => (h s hs).symm

theorem bondConnected_trans (left right : E → V) (η : E → Bool) {x y z : V}
    (h : bondConnected left right η x y) (k : bondConnected left right η y z) :
    bondConnected left right η x z := fun s hs => (h s hs).trans (k s hs)

theorem bondConnected_endpoints (left right : E → V) (η : E → Bool) (e : E) (he : η e=true) :
    bondConnected left right η (left e) (right e) := fun _ hs => hs e he

theorem compatibleSigns_connected (left right : E → V) (η : E → Bool)
    {s : V → Bool} (hs : s∈compatibleSigns left right η) {x y : V}
    (h : bondConnected left right η x y) : s x=s y := by
  apply signFieldEquiv.injective
  apply h
  intro e he
  exact congrArg signFieldEquiv (hs e he)

def prescribedCompatibleSigns (left right : E → V) (B : Set V) (p : V → Bool) (η : E → Bool) : Set (V → Bool) :=
  {s | s∈compatibleSigns left right η ∧ ∀ v∈B,s v=p v}

def signTranslate (t : V → Bool) : (V → Bool) ≃ (V → Bool) where
  toFun s v := s v==t v
  invFun s v := s v==t v
  left_inv s := by funext v; change ((s v==t v)==t v)=s v; cases s v <;> cases t v <;> rfl
  right_inv s := by funext v; change ((s v==t v)==t v)=s v; cases s v <;> cases t v <;> rfl

theorem signTranslate_compatible (left right : E → V) (η : E → Bool) (t : V → Bool)
    (ht : t∈compatibleSigns left right η) (s : V → Bool) :
    signTranslate t s∈compatibleSigns left right η ↔ s∈compatibleSigns left right η := by
  change (∀ e,η e=true → (s (left e)==t (left e))=(s (right e)==t (right e))) ↔ _
  constructor
  · intro h e he
    have h' := h e he
    rw [ht e he] at h'
    have hc (a b c : Bool) : (a==c)=(b==c) ↔ a=b := by
      cases a <;> cases b <;> cases c <;> decide
    exact (hc _ _ _).mp h'
  · intro h e he
    rw [h e he,ht e he]

def prescribedCompatibleSignsEquiv (left right : E → V) (B : Set V) (p : V → Bool) (η : E → Bool)
    (t : prescribedCompatibleSigns left right B p η) :
    positiveCompatibleSigns left right B η ≃ prescribedCompatibleSigns left right B p η :=
  (signTranslate t.val).subtypeEquiv (by
    intro s
    change (s∈compatibleSigns left right η ∧ ∀ v∈B,s v=true) ↔
      (signTranslate t.val s∈compatibleSigns left right η ∧ ∀ v∈B,(s v==t.val v)=p v)
    rw [signTranslate_compatible left right η t.val t.property.1]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro v
    apply forall_congr'
    intro hv
    rw [← t.property.2 v hv]
    cases s v <;> cases t.val v <;> decide)

variable [Fintype V]

theorem prescribedCompatibleSigns_card_of_nonempty (left right : E → V) (B : Set V)
    (p : V → Bool) (η : E → Bool) (h : (prescribedCompatibleSigns left right B p η).Nonempty) :
    (Fintype.card (prescribedCompatibleSigns left right B p η):ℝ)=
      clusterWeight left right η*bondPinFactor left right B η := by
  obtain ⟨t,ht⟩ := h
  rw [← Fintype.card_congr (prescribedCompatibleSignsEquiv left right B p η ⟨t,ht⟩)]
  exact positiveCompatibleSigns_card _ _ _ _

def bondCrossing (left right : E → V) (I O : Set V) (η : E → Bool) : Prop :=
  ∃ x∈I,∃ y∈O,bondConnected left right η x y

def layerSigns (I : Set V) (v : V) : Bool := if v∈I then false else true

omit [Fintype V] in
theorem layerSigns_consistent_iff (left right : E → V) (I O : Set V) (hIO : Disjoint I O)
    (η : E → Bool) : (prescribedCompatibleSigns left right (I∪O) (layerSigns I) η).Nonempty ↔
      ¬bondCrossing left right I O η := by
  constructor
  · rintro ⟨s,hs,hp⟩ ⟨x,hx,y,hy,hxy⟩
    have he := compatibleSigns_connected left right η hs hxy
    have hx' := hp x (Or.inl hx)
    have hy' := hp y (Or.inr hy)
    have hyI : y∉I := fun h => Set.disjoint_left.mp hIO h hy
    simp only [layerSigns,hx,hyI,ite_true,ite_false] at hx' hy'
    rw [hx',hy'] at he
    cases he
  · intro hn
    let t : V → Bool := fun v => if ∃ x∈I,bondConnected left right η x v then false else true
    refine ⟨t,?_,?_⟩
    · intro e he
      have hc := bondConnected_endpoints left right η e he
      have hi : (∃ x∈I,bondConnected left right η x (left e)) ↔
          ∃ x∈I,bondConnected left right η x (right e) := by
        constructor
        · rintro ⟨x,hx,hxc⟩
          exact ⟨x,hx,bondConnected_trans left right η hxc hc⟩
        · rintro ⟨x,hx,hxc⟩
          exact ⟨x,hx,bondConnected_trans left right η hxc (bondConnected_symm left right η hc)⟩
      simp only [t,hi]
    · intro v hv
      rcases hv with hv | hv
      · have hc : ∃ x∈I,bondConnected left right η x v := ⟨v,hv,bondConnected_refl _ _ _ _⟩
        simp [t,layerSigns,hv,hc]
      · have hc : ¬∃ x∈I,bondConnected left right η x v := by
          rintro ⟨x,hx,hxv⟩
          exact hn ⟨x,hx,v,hv,hxv⟩
        have hvI : v∉I := fun h => Set.disjoint_left.mp hIO h hv
        simp [t,layerSigns,hvI,hc]

theorem layerSigns_card (left right : E → V) (I O : Set V) (hIO : Disjoint I O) (η : E → Bool) :
    (Fintype.card (prescribedCompatibleSigns left right (I∪O) (layerSigns I) η):ℝ)=
      clusterWeight left right η*bondPinFactor left right (I∪O) η*
        (if bondCrossing left right I O η then 0 else 1) := by
  split_ifs with h
  · have he : prescribedCompatibleSigns left right (I∪O) (layerSigns I) η=∅ := by
      exact Set.not_nonempty_iff_eq_empty.mp (fun hn => (layerSigns_consistent_iff _ _ _ _ hIO _).mp hn h)
    simp [he]
  · rw [prescribedCompatibleSigns_card_of_nonempty _ _ _ _ _ ((layerSigns_consistent_iff _ _ _ _ hIO _).mpr h)]
    simp

end ClassicalON

end

end OAI
