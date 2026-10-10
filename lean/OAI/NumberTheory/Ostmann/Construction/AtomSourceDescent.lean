import Mathlib.Data.Fin.Tuple.Basic
import OAI.NumberTheory.Ostmann.Construction.AtomAncestorSources

namespace OAI

/-! # Actual reverse paths with freshly indexed ancestor pivot sources -/

namespace Ostmann
open scoped Classical

def AtomSourceBefore {B : Type*} (d : ℕ) : B ⊕ ℕ → Prop
  | .inl _ => True
  | .inr j => j < d

theorem AtomSourceBefore.mono {B : Type*} {d e : ℕ} {s : B ⊕ ℕ}
    (h : AtomSourceBefore d s) (hde : d ≤ e) : AtomSourceBefore e s := by
  cases s with
  | inl _ => trivial
  | inr j => exact lt_of_lt_of_le h hde

noncomputable def advanceNatAtomSources {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ) :
    CopyScheduleAtoms role n → B ⊕ ℕ := reverseCopyLabelMap role n b (.inr d) source

theorem advanceNatAtomSources_before {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ)
    (hs : ∀ v, AtomSourceBefore d (source v)) :
    ∀ v, AtomSourceBefore (d + 1) (advanceNatAtomSources role n d b source v) := by
  intro v
  unfold advanceNatAtomSources reverseCopyLabelMap
  split_ifs
  · exact (hs _).mono (Nat.le_succ d)
  · exact Nat.lt_succ_self d
  · exact (hs _).mono (Nat.le_succ d)

theorem advanceNatAtomSources_injective {I B : Type*} (role : I → CopyScheduleRole)
    (n d : ℕ) (b : Bool) (source : CopyScheduleAtoms role (n + 1) → B ⊕ ℕ)
    (hinj : Function.Injective source) (hs : ∀ v, AtomSourceBefore d (source v))
    (hu : ∀ i j, role i = .pivot n → role j = .pivot n → i = j) :
    Function.Injective (advanceNatAtomSources role n d b source) := by
  apply reverseCopyLabelMap_injective role n b hu _ source hinj
  intro v hv
  have h := hs v
  rw [hv] at h
  exact Nat.lt_irrefl d h

/-- The first entry of the path is the root branch. Source indices count
the previously reconstructed pivots in root-to-leaf order. -/
noncomputable def descendAtomSources {I B : Type*} (role : I → CopyScheduleRole) :
    (h n d : ℕ) → (Fin h → Bool) → (CopyScheduleAtoms role (n + h) → B ⊕ ℕ) →
      CopyScheduleAtoms role n → B ⊕ ℕ
  | 0, _, _, _, source => source
  | h + 1, n, d, path, source =>
    descendAtomSources role h n (d + 1) (Fin.tail path)
      (advanceNatAtomSources role (n + h) d (path 0) source)

theorem descendAtomSources_before {I B : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (hs : ∀ v, AtomSourceBefore d (source v)) :
    ∀ v, AtomSourceBefore (d + h) (descendAtomSources role h n d path source v) := by
  induction h generalizing d with
  | zero => exact hs
  | succ h ih =>
    have hp := ih (d + 1) (Fin.tail path) _
      (advanceNatAtomSources_before role (n + h) d (path 0) source hs)
    intro v
    exact (hp v).mono (by omega)

theorem descendAtomSources_injective {I B : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (hinj : Function.Injective source) (hs : ∀ v, AtomSourceBefore d (source v))
    (hu : ∀ j < n + h, ∀ a b, role a = .pivot j → role b = .pivot j → a = b) :
    Function.Injective (descendAtomSources role h n d path source) := by
  induction h generalizing d with
  | zero => exact hinj
  | succ h ih =>
    exact ih (d + 1) (Fin.tail path) _
      (advanceNatAtomSources_injective role (n + h) d (path 0) source hinj hs (hu _ (by omega)))
      (advanceNatAtomSources_before role (n + h) d (path 0) source hs)
      (fun j hj => hu j (by omega))

noncomputable def descendAtomValues {I A : Type*} (role : I → CopyScheduleRole) :
    (h n d : ℕ) → (Fin h → Bool) → (ℕ → A) → (CopyScheduleAtoms role (n + h) → A) →
      CopyScheduleAtoms role n → A
  | 0, _, _, _, _, current => current
  | h + 1, n, d, path, p, current =>
    descendAtomValues role h n (d + 1) (Fin.tail path) p
      (reverseCopyLabelMap role (n + h) (path 0) (p d) current)

/-- Evaluating symbolic sources agrees exactly with the successive integer
substitutions. This equality does not discard any pivot or outside coordinate. -/
theorem descendAtomSources_eval {I B A : Type*} (role : I → CopyScheduleRole)
    (h n d : ℕ) (path : Fin h → Bool) (source : CopyScheduleAtoms role (n + h) → B ⊕ ℕ)
    (C : B → A) (p : ℕ → A) (v : CopyScheduleAtoms role n) :
    Sum.elim C p (descendAtomSources role h n d path source v) =
      descendAtomValues role h n d path p (fun w => Sum.elim C p (source w)) v := by
  induction h generalizing d with
  | zero => rfl
  | succ h ih =>
    change Sum.elim C p
      (descendAtomSources role h n (d + 1) (Fin.tail path)
        (advanceNatAtomSources role (n + h) d (path 0) source) v) = _
    rw [ih]
    congr 1
    funext w
    exact reverseCopyLabelMap_map role (n + h) (path 0) (.inr d) source (Sum.elim C p) w

end Ostmann

end OAI
