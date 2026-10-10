import OAI.NumberTheory.Ostmann.Construction.AtomSourceDescent
import OAI.NumberTheory.Ostmann.Construction.ScheduledSourceScheme

namespace OAI

/-! # Concrete ancestor-source environments at every scheduled tree node -/

namespace Ostmann
open scoped Classical

noncomputable def boundAtomSources {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (a : A) : B ⊕ Fin d :=
  match h : source a with
  | .inl b => .inl b
  | .inr j => .inr ⟨j, by simpa only [h, AtomSourceBefore] using hs a⟩

theorem boundAtomSources_unbound {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (a : A) :
    Sum.map id Fin.val (boundAtomSources d source hs a) = source a := by
  unfold boundAtomSources
  split <;> rename_i v hv
  all_goals exact hv.symm

theorem boundAtomSources_injective {A B : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (hinj : Function.Injective source) :
    Function.Injective (boundAtomSources d source hs) := by
  intro a b h
  apply hinj
  have he := congrArg (Sum.map id Fin.val) h
  simpa only [boundAtomSources_unbound] using he

theorem boundAtomSources_eval {A B M : Type*} (d : ℕ) (source : A → B ⊕ ℕ)
    (hs : ∀ a, AtomSourceBefore d (source a)) (C : B → M) (p : ℕ → M) (a : A) :
    Sum.elim C (fun j : Fin d => p j.val) (boundAtomSources d source hs a) =
      Sum.elim C p (source a) := by
  unfold boundAtomSources
  split <;> rename_i v hv
  all_goals exact (congrArg (Sum.elim C p) hv).symm

def scheduledReversePath (n : ℕ) (j : Fin (2 ^ n - 1)) :
    Fin (preorderNodePath n j).length → Bool :=
  fun a => !((preorderNodePath n j)[a.val])

abbrev scheduledNodeLevel (n : ℕ) (j : Fin (2 ^ n - 1)) : ℕ :=
  n - ((preorderNodePath n j).length + 1)

theorem scheduledNodeLevel_add_depth (n : ℕ) (j : Fin (2 ^ n - 1)) :
    scheduledNodeLevel n j + 1 + (preorderNodePath n j).length = n := by
  have h := preorderNodePath_length n j
  dsimp only [scheduledNodeLevel]
  omega

noncomputable def scheduledNodeRootEquiv {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1 + (preorderNodePath n j).length) ≃
      CopyScheduleAtoms role n :=
  Equiv.cast (congrArg (CopyScheduleAtoms role) (scheduledNodeLevel_add_depth n j))

noncomputable def scheduledRawNodeSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) → CopyScheduleAtoms role n ⊕ ℕ :=
  descendAtomSources role (preorderNodePath n j).length (scheduledNodeLevel n j + 1) 0
    (scheduledReversePath n j) (fun v => .inl (scheduledNodeRootEquiv role n j v))

theorem scheduledRawNodeSources_before {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    ∀ v, AtomSourceBefore (preorderNodePath n j).length (scheduledRawNodeSources role n j v) := by
  simpa only [Nat.zero_add, scheduledRawNodeSources] using descendAtomSources_before role (preorderNodePath n j).length
    (scheduledNodeLevel n j + 1) 0 (scheduledReversePath n j)
    (fun v => Sum.inl (scheduledNodeRootEquiv role n j v)) (fun _ => True.intro)

theorem scheduledRawNodeSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledRawNodeSources role n j) := by
  apply descendAtomSources_injective role _ _ 0 _ _
    (Sum.inl_injective.comp (scheduledNodeRootEquiv role n j).injective) (fun _ => trivial)
  intro k hk
  rw [scheduledNodeLevel_add_depth] at hk
  exact hu k hk

noncomputable def scheduledNodeSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1)) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) →
      CopyScheduleAtoms role n ⊕ Fin (preorderNodePath n j).length :=
  boundAtomSources _ _ (scheduledRawNodeSources_before role n j)

theorem scheduledNodeSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledNodeSources role n j) :=
  boundAtomSources_injective _ _ _ (scheduledRawNodeSources_injective role n j hu)

noncomputable def scheduledNodeHSources {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (j : Fin (2 ^ n - 1)) :
    CopyScheduleH role (scheduledNodeLevel n j) →
      CopyScheduleAtoms role n ⊕ Fin (preorderNodePath n j).length :=
  fun h => scheduledNodeSources role n j ⟨.inl (b, h.val), h.property⟩

theorem scheduledNodeHSources_injective {I : Type*} (role : I → CopyScheduleRole)
    (n : ℕ) (b : Bool) (j : Fin (2 ^ n - 1))
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b) :
    Function.Injective (scheduledNodeHSources role n b j) := by
  intro v w h
  have he := scheduledNodeSources_injective role n j hu h
  apply Subtype.ext
  exact congrArg Prod.snd (Sum.inl.inj (congrArg Subtype.val he))

/-- In v H_R - w H_L, the left coefficient is the right H source product. -/
noncomputable def scheduledActualSourceScheme {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (S : Finset ℤ) (n : ℕ) (t : FrequencyTree S n)
    (C : CopyScheduleAtoms role n → ℤ) : PivotDependencyScheme (2 ^ n - 1) :=
  scheduledSourceScheme role S n t
    (scheduledNodeHSources role n false) (scheduledNodeHSources role n true) C

noncomputable def nodeAncestorValues {A : Type*} [Zero A] (n : ℕ) (j : Fin (2 ^ n - 1))
    (p : Fin (2 ^ n - 1) → A) (k : ℕ) : A :=
  if hk : k < (preorderNodePath n j).length then p (ancestorNodeIndex n j ⟨k, hk⟩) else 0

noncomputable def scheduledNodeValues {I A : Type*} [Zero A] (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (C : CopyScheduleAtoms role n → A) (p : Fin (2 ^ n - 1) → A) :
    CopyScheduleAtoms role (scheduledNodeLevel n j + 1) → A :=
  descendAtomValues role (preorderNodePath n j).length (scheduledNodeLevel n j + 1) 0
    (scheduledReversePath n j) (nodeAncestorValues n j p)
    (fun v => C (scheduledNodeRootEquiv role n j v))

/-- The finite source encoding evaluates to the actual assignment reached
by the ancestor substitutions along this node's path. -/
theorem scheduledNodeSources_eval {I A : Type*} [Zero A] (role : I → CopyScheduleRole)
    (n : ℕ) (j : Fin (2 ^ n - 1))
    (C : CopyScheduleAtoms role n → A) (p : Fin (2 ^ n - 1) → A)
    (v : CopyScheduleAtoms role (scheduledNodeLevel n j + 1)) :
    Sum.elim C (fun a => p (ancestorNodeIndex n j a)) (scheduledNodeSources role n j v) =
      scheduledNodeValues role n j C p v := by
  have hp : (fun a : Fin (preorderNodePath n j).length => nodeAncestorValues n j p a.val) =
      (fun a => p (ancestorNodeIndex n j a)) := by
    funext a
    exact dite_eq_left a.isLt
  rw [← hp]
  change Sum.elim C (fun a : Fin (preorderNodePath n j).length => nodeAncestorValues n j p a.val)
    (boundAtomSources _ _ _ v) = _
  rw [boundAtomSources_eval]
  exact descendAtomSources_eval role (preorderNodePath n j).length
    (scheduledNodeLevel n j + 1) 0 (scheduledReversePath n j)
    (fun w => Sum.inl (scheduledNodeRootEquiv role n j w)) C (nodeAncestorValues n j p) v

end Ostmann

end OAI
