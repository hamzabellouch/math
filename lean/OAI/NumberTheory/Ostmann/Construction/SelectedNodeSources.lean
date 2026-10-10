import OAI.NumberTheory.Ostmann.Construction.ScheduledNodeSources
import OAI.NumberTheory.Ostmann.Construction.SelectedWordReversal

namespace OAI

/-! # Ancestor coefficients exclude every unexposed selected word prime -/

namespace Ostmann
open scoped Classical

/-- A property of the outside coordinates survives one literal reversal. -/
theorem reverseCopyLabelMap_wordOutside_property {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (b : Bool) (P : A) (current : CopyScheduleAtoms role (n + 1) → A)
    (F : A → Prop) (hP : F P)
    (hcurrent : ∀ v : WordLeafOutside role i hi (n + 1), F (current v.val))
    (v : WordLeafOutside role i hi n) :
    F (reverseCopyLabelMap role n b P current v.val) := by
  by_cases hc : (copyScheduleRole role n v.val.val).copiedAt n = true
  · let h : CopyScheduleH role n := ⟨v.val.val, v.val.property, hc⟩
    have hh : h ∉ Set.range (wordLeafHSlot role i hi n) := by
      rintro ⟨t, ht⟩
      apply v.property
      exact ⟨t, Subtype.ext (congrArg (fun h : CopyScheduleH role n => h.val) ht)⟩
    rw [reverseCopyLabelMap, dite_eq_left hc]
    exact hcurrent (copiedWordLeafOutside role i hi n b ⟨h, hh⟩)
  · by_cases he : (copyScheduleRole role n v.val.val).erasedAt n = true
    · rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_left he]
      exact hP
    · let z : WordLeafOutside role i hi (n + 1) :=
        ⟨⟨.inr v.val.val, v.val.property, Bool.eq_false_iff.mpr hc, Bool.eq_false_iff.mpr he⟩, by
          rintro ⟨t, ht⟩
          have hv := congrArg (fun a : CopyScheduleAtoms role (n + 1) => a.val) ht
          cases t with
          | inl t => rw [wordLeafSlot_left] at hv; cases hv
          | inr t => rw [wordLeafSlot_right] at hv; cases hv⟩
      rw [reverseCopyLabelMap, dite_eq_right hc, dite_eq_right he]
      exact hcurrent z

/-- The whole path uses only initial outside coordinates and earlier pivots. -/
theorem descendAtomSources_wordOutside {I B : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (h n d : ℕ) (path : Fin h → Bool)
    (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ) (F : B ⊕ ℕ → Prop)
    (hsource : ∀ v : WordLeafOutside role i hi (n + h), F (source v.val))
    (hpivot : ∀ k, d ≤ k → k < d + h → F (.inr k)) :
    ∀ v : WordLeafOutside role i hi n,
      F (descendAtomSources role h n d path source v.val) := by
  induction h generalizing d with
  | zero => exact hsource
  | succ h ih =>
    apply ih (d + 1) (Fin.tail path)
    · intro v
      exact reverseCopyLabelMap_wordOutside_property role i hi (n + h) (path 0)
        (.inr d) source F (hpivot d le_rfl (by omega)) hsource v
    · intro k hk hk'
      exact hpivot k (by omega) (by omega)

def WordSourceOutside {I : Type*} (role : I → CopyScheduleRole)
    (i : I) (hi : role i = .word) (n : ℕ) : CopyScheduleAtoms role n ⊕ ℕ → Prop
  | .inl v => v ∉ Set.range (wordLeafSlot role i hi n)
  | .inr _ => True

theorem scheduledRawNodeSources_wordOutside {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1)) (v : WordLeafOutside role i hi (scheduledNodeLevel n j + 1)) :
    WordSourceOutside role i hi n (scheduledRawNodeSources role n j v.val) := by
  apply descendAtomSources_wordOutside role i hi _ _ 0 _ _
  · intro w
    change scheduledNodeRootEquiv role n j w.val ∉ Set.range (wordLeafSlot role i hi n)
    have hcast : ∀ {m n : ℕ} (h : m = n) (w : WordLeafOutside role i hi m),
        Equiv.cast (congrArg (CopyScheduleAtoms role) h) w.val ∉
          Set.range (wordLeafSlot role i hi n) := by
      intro m n h w
      subst n
      exact w.property
    exact hcast (scheduledNodeLevel_add_depth n j) w
  · intro _ _ _
    trivial

/-- Restricting the source type does not change the value or identify sources. -/
noncomputable def selectedNodeSources {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (v : WordLeafOutside role i hi (scheduledNodeLevel n j + 1)) :
    WordLeafOutside role i hi n ⊕ Fin (preorderNodePath n j).length :=
  match hs : scheduledNodeSources role n j v.val with
  | .inl a => .inl ⟨a, by
      have ho := scheduledRawNodeSources_wordOutside role i hi n j v
      have he := boundAtomSources_unbound _ _ (scheduledRawNodeSources_before role n j) v.val
      change Sum.map id Fin.val (scheduledNodeSources role n j v.val) = _ at he
      rw [hs] at he
      rw [← he] at ho
      exact ho⟩
  | .inr k => .inr k

theorem selectedNodeSources_unbound {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (v : WordLeafOutside role i hi (scheduledNodeLevel n j + 1)) :
    Sum.map Subtype.val id (selectedNodeSources role i hi n j v) =
      scheduledNodeSources role n j v.val := by
  unfold selectedNodeSources
  split <;> rename_i a ha <;> exact ha.symm

theorem selectedNodeSources_injective {I : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (selectedNodeSources role i hi n j) := by
  intro a b h
  have he := congrArg (Sum.map Subtype.val id) h
  rw [selectedNodeSources_unbound, selectedNodeSources_unbound] at he
  exact Subtype.ext (scheduledNodeSources_injective role n j hu he)

theorem selectedNodeSources_eval {I A : Type*}
    (role : I → CopyScheduleRole) (i : I) (hi : role i = .word)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (y : WordLeafOutside role i hi n → A) (x : TreeLeafIndex n → A)
    (p : Fin (preorderNodePath n j).length → A)
    (v : WordLeafOutside role i hi (scheduledNodeLevel n j + 1)) :
    Sum.elim y p (selectedNodeSources role i hi n j v) =
      Sum.elim (wordLeafAssignment role i hi n y x) p (scheduledNodeSources role n j v.val) := by
  have he := selectedNodeSources_unbound role i hi n j v
  rw [← he]
  cases selectedNodeSources role i hi n j v with
  | inl a => exact (wordLeafAssignment_outside role i hi n y x a).symm
  | inr k => rfl

end Ostmann

end OAI
