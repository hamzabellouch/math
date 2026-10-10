import OAI.Computability.TypeSystem.Typing

namespace OAI

namespace PureTypeSystem

universe u

deriving instance Countable for Expr

namespace Expr

variable {S : Type u}

/-- Every free index is below the context length. -/
def Scoped : Nat → Expr S → Prop
  | n, .var i => i < n
  | _, .sort _ => True
  | n, .app M N => Scoped n M ∧ Scoped n N
  | n, .lam A b => Scoped n A ∧ Scoped (n+1) b
  | n, .pi A B => Scoped n A ∧ Scoped (n+1) B

namespace Scoped

variable {n m : Nat} {M : Expr S}

theorem rename (h : Scoped n M) (ρ : Nat → Nat)
    (hρ : ∀ i, i < n → ρ i < m) : Scoped m (M.rename ρ) := by
  induction M generalizing n m ρ with
  | var i => exact hρ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hρ, ihN h.2 _ hρ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hρ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i => exact Nat.succ_lt_succ (hρ i (Nat.lt_of_succ_lt_succ hi))

theorem mono (h : Scoped n M) (hnm : n ≤ m) : Scoped m M := by
  simpa only [rename_id] using h.rename id (fun _ hi => lt_of_lt_of_le hi hnm)

theorem rename_congr (h : Scoped n M) {ρ τ : Nat → Nat}
    (he : ∀ i, i < n → ρ i = τ i) : M.rename ρ = M.rename τ := by
  induction M generalizing n ρ τ with
  | var i => exact congrArg Expr.var (he i h)
  | sort _ => rfl
  | app M N ihM ihN => exact congrArg₂ Expr.app (ihM h.1 he) (ihN h.2 he)
  | lam A b ihA ihb | pi A b ihA ihb =>
      have hl : ∀ i, i < n+1 → liftRen ρ i = liftRen τ i := by
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact congrArg Nat.succ (he i (Nat.lt_of_succ_lt_succ hi))
      simp only [Expr.rename, ihA h.1 he, ihb h.2 hl]

theorem subst (h : Scoped n M) (σ : Nat → Expr S)
    (hσ : ∀ i, i < n → Scoped m (σ i)) : Scoped m (M.subst σ) := by
  induction M generalizing n m σ with
  | var i => exact hσ i h
  | sort _ => trivial
  | app M N ihM ihN => exact ⟨ihM h.1 _ hσ, ihN h.2 _ hσ⟩
  | lam A b ihA ihb | pi A b ihA ihb =>
      refine ⟨ihA h.1 _ hσ, ihb h.2 _ ?_⟩
      intro i hi
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i =>
          exact (hσ i (Nat.lt_of_succ_lt_succ hi)).rename Nat.succ
            (fun _ hi => Nat.succ_lt_succ hi)

theorem instantiate {b a : Expr S} (hb : Scoped (n+1) b) (ha : Scoped n a) :
    Scoped n (b.instantiate a) := by
  apply hb.subst
  intro i hi
  cases i with
  | zero => exact ha
  | succ i => exact Nat.lt_of_succ_lt_succ hi

end Scoped

/-- Reversal identifies de Bruijn indices in a finite context with fixed levels.
Outside that context it is the identity. -/
def reverseIndex (n i : Nat) : Nat := if i < n then n - 1 - i else i

theorem reverseIndex_lt {n i : Nat} (hi : i < n) : reverseIndex n i < n := by
  simp only [reverseIndex, ite_eq_left hi]
  omega

theorem reverseIndex_involutive (n : Nat) : Function.Involutive (reverseIndex n) := by
  intro i
  unfold reverseIndex
  split_ifs <;> omega

@[simp] theorem reverseIndex_twice (n : Nat) (M : Expr S) :
    (M.rename (reverseIndex n)).rename (reverseIndex n) = M := by
  rw [rename_comp]
  have he : reverseIndex n ∘ reverseIndex n = id := funext (reverseIndex_involutive n)
  rw [he, rename_id]

theorem Scoped.reverseIndex {n : Nat} {M : Expr S} (h : Scoped n M) :
    Scoped n (M.rename (reverseIndex n)) :=
  h.rename _ (fun _ hi => reverseIndex_lt hi)

theorem Scoped.reverseIndex_succ {n : Nat} {M : Expr S} (h : Scoped n M) :
    M.rename (Expr.reverseIndex (n+1)) = (M.rename (Expr.reverseIndex n)).rename Nat.succ := by
  rw [rename_comp]
  apply h.rename_congr
  intro i hi
  simp only [Function.comp_apply, Expr.reverseIndex, ite_eq_left hi]
  rw [ite_eq_left (Nat.lt_succ_of_lt hi)]
  omega

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)} {M A : Expr S}

theorem scope (h : HasType P Γ M A) : M.Scoped Γ.length ∧ A.Scoped Γ.length := by
  induction h with
  | ax _ => exact ⟨True.intro, True.intro⟩
  | var _ ih =>
      exact ⟨Nat.zero_lt_succ _, ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | weaken _ _ ih _ =>
      exact ⟨ih.1.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi),
        ih.2.rename Nat.succ (fun _ hi => Nat.succ_lt_succ hi)⟩
  | product _ _ _ ihA ihB => exact ⟨⟨ihA.1, ihB.1⟩, True.intro⟩
  | abstraction _ _ ihb ihPi => exact ⟨⟨ihPi.1.1, ihb.1⟩, ihPi.1⟩
  | application _ _ ihf iha => exact ⟨⟨ihf.1, iha.1⟩, ihf.2.2.instantiate iha.1⟩
  | conversion _ _ _ ihM ihB => exact ⟨ihM.1, ihB.1⟩

end HasType

namespace Beta

variable {S : Type u} {M N : Expr S}

theorem scope (h : Beta M N) {n : Nat} (hM : M.Scoped n) : N.Scoped n := by
  induction h generalizing n with
  | head _ _ _ => exact hM.1.2.instantiate hM.2
  | app_left _ ih => exact ⟨ih hM.1, hM.2⟩
  | app_right _ ih => exact ⟨hM.1, ih hM.2⟩
  | lam_domain _ ih | pi_domain _ ih => exact ⟨ih hM.1, hM.2⟩
  | lam_body _ ih | pi_body _ ih => exact ⟨hM.1, ih hM.2⟩

end Beta

namespace Reduces

variable {S : Type u} {M N : Expr S}

theorem scope (h : Reduces M N) {n : Nat} (hM : M.Scoped n) : N.Scoped n := by
  induction h with
  | refl => exact hM
  | tail _ h ih => exact h.scope ih

end Reduces

namespace WeaklyNormalizing

variable {S : Type u} {M : Expr S}

theorem rename (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    WeaklyNormalizing (M.rename ρ) := by
  obtain ⟨N, hr, hn⟩ := h
  exact ⟨N.rename ρ, Reduces.rename hr ρ, hn.rename ρ⟩

theorem reverseIndex_iff (n : Nat) :
    WeaklyNormalizing (M.rename (Expr.reverseIndex n)) ↔ WeaklyNormalizing M := by
  constructor
  · intro h
    simpa only [Expr.reverseIndex_twice] using h.rename (Expr.reverseIndex n)
  · intro h
    exact h.rename _

end WeaklyNormalizing

/-- Finite prefixes of a common context, using fixed-level names when viewed
outside a prefix. Every sortable fixed-level expression is declared arbitrarily
late. Bound variables remain de Bruijn indices and are never declared here. -/
structure ContextTower {S : Type u} (P : Specification S) where
  context : Nat → List (Expr S)
  valid : ∀ n, ValidContext P (context n)
  length : ∀ n, (context n).length = n
  step : ∀ n, ∃ A s, HasType P (context n) A (.sort s) ∧ context (n+1) = A :: context n
  saturated : ∀ (n : Nat) (A : Expr S) (s : S), HasType P (context n) (A.rename (Expr.reverseIndex n)) (.sort s) →
    ∀ lower, ∃ m, n ≤ m ∧ lower ≤ m ∧
      context (m+1) = A.rename (Expr.reverseIndex m) :: context m

namespace ContextTowerConstruction

variable {S : Type u} (P : Specification S)

structure Stage (n : Nat) where
  context : List (Expr S)
  valid : ValidContext P context
  length : context.length = n

variable [Countable S]

noncomputable def enumeration : Nat → Expr S := by
  letI : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose

theorem enumeration_surjective : Function.Surjective (enumeration (S := S)) := by
  let : Nonempty (Expr S) := ⟨.var 0⟩
  exact (exists_surjective_nat (Expr S)).choose_spec

noncomputable def scheduled (n : Nat) : Expr S := enumeration (Nat.unpair n).1

theorem scheduled_late (A : Expr S) (lower : Nat) :
    ∃ m, lower ≤ m ∧ scheduled m = A := by
  obtain ⟨k, hk⟩ := enumeration_surjective A
  exact ⟨Nat.pair k lower, Nat.right_le_pair _ _, by simpa only [scheduled, Nat.unpair_pair]⟩

variable {s₀ t₀ : S} (h₀ : P.axioms s₀ t₀)

noncomputable def next {n : Nat} (Γ : Stage P n) :
    {A : Expr S // ∃ s, HasType P Γ.context A (.sort s)} := by
  classical
  let A : Expr S := (scheduled n).rename (Expr.reverseIndex n)
  exact if ht : ∃ s, HasType P Γ.context A (.sort s) then ⟨A, ht⟩
    else ⟨.sort s₀, t₀, HasType.sort_of_valid Γ.valid h₀⟩

noncomputable def stages : (n : Nat) → Stage P n
  | 0 => ⟨[], .nil, rfl⟩
  | n+1 =>
      let Γ := stages n
      let A := next P h₀ Γ
      ⟨A.val :: Γ.context, .cons Γ.valid A.property.choose_spec,
        by simp only [List.length_cons, Γ.length]⟩

noncomputable def contexts (n : Nat) : List (Expr S) := (stages P h₀ n).context

theorem valid (n : Nat) : ValidContext P (contexts P h₀ n) := (stages P h₀ n).valid

theorem length (n : Nat) : (contexts P h₀ n).length = n := (stages P h₀ n).length

theorem step (n : Nat) : ∃ A s, HasType P (contexts P h₀ n) A (.sort s) ∧
    contexts P h₀ (n+1) = A :: contexts P h₀ n :=
  ⟨(next P h₀ (stages P h₀ n)).val, _, (next P h₀ (stages P h₀ n)).property.choose_spec, rfl⟩

theorem rename_next {n : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    HasType P (contexts P h₀ (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := step P h₀ n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem rename_mono {n m : Nat} {M A : Expr S}
    (h : HasType P (contexts P h₀ n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    HasType P (contexts P h₀ m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact rename_next P h₀ ih

theorem at_scheduled {n : Nat} (s : S)
    (h : HasType P (contexts P h₀ n) ((scheduled n).rename (Expr.reverseIndex n)) (.sort s)) :
    contexts P h₀ (n+1) = (scheduled n).rename (Expr.reverseIndex n) :: contexts P h₀ n := by
  classical
  have ht : ∃ t, HasType P (stages P h₀ n).context
      ((scheduled n).rename (Expr.reverseIndex n)) (.sort t) := ⟨s,h⟩
  simp only [contexts, stages, next, dite_eq_left ht]

theorem saturated (n : Nat) (A : Expr S) (s : S)
    (h : HasType P (contexts P h₀ n) (A.rename (Expr.reverseIndex n)) (.sort s))
    (lower : Nat) : ∃ m, n ≤ m ∧ lower ≤ m ∧
      contexts P h₀ (m+1) = A.rename (Expr.reverseIndex m) :: contexts P h₀ m := by
  obtain ⟨m, hm, he⟩ := scheduled_late A (max n lower)
  have hnm : n ≤ m := (le_max_left _ _).trans hm
  have hlm : lower ≤ m := (le_max_right _ _).trans hm
  have ht : HasType P (contexts P h₀ m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    rename_mono P h₀ (A := .sort s) h hnm
  refine ⟨m, hnm, hlm, ?_⟩
  have hs : HasType P (contexts P h₀ m)
      ((scheduled m).rename (Expr.reverseIndex m)) (.sort s) := by
    rw [he]
    exact ht
  calc
    contexts P h₀ (m+1) = (scheduled m).rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      at_scheduled P h₀ s hs
    _ = A.rename (Expr.reverseIndex m) :: contexts P h₀ m :=
      congrArg (fun B : Expr S => B.rename (Expr.reverseIndex m) :: contexts P h₀ m) he

noncomputable def tower : ContextTower P where
  context := contexts P h₀
  valid := valid P h₀
  length := length P h₀
  step := step P h₀
  saturated := saturated P h₀

end ContextTowerConstruction

namespace ContextTower

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- A global judgment is witnessed in a finite prefix of the tower. -/
def HasType (M A : Expr S) : Prop :=
  ∃ n, PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
    (A.rename (Expr.reverseIndex n))

theorem at_next {n : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) :
    PureTypeSystem.HasType P (Ω.context (n+1)) (M.rename (Expr.reverseIndex (n+1)))
      (A.rename (Expr.reverseIndex (n+1))) := by
  have hm : M.Scoped n := by
    have hh := h.scope.1.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  have ha : A.Scoped n := by
    have hh := h.scope.2.reverseIndex
    rw [Ω.length, Expr.reverseIndex_twice] at hh
    exact hh
  obtain ⟨D, s, ht, he⟩ := Ω.step n
  rw [he, hm.reverseIndex_succ, ha.reverseIndex_succ]
  exact .weaken h ht

theorem at_mono {n m : Nat} {M A : Expr S}
    (h : PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n))) (hnm : n ≤ m) :
    PureTypeSystem.HasType P (Ω.context m) (M.rename (Expr.reverseIndex m))
      (A.rename (Expr.reverseIndex m)) := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact Ω.at_next ih

namespace HasType

variable {Ω : ContextTower P} {M A : Expr S}

theorem scope (h : Ω.HasType M A) : ∃ n, M.Scoped n ∧ A.Scoped n := by
  obtain ⟨n, ht⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  · have hh := ht.scope.2.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh

theorem weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing M := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inl ht⟩)

theorem type_weaklyNormalizing (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    WeaklyNormalizing A := by
  obtain ⟨n, ht⟩ := h
  exact (WeaklyNormalizing.reverseIndex_iff n).mp (hw _ ht.valid _ ⟨_, Or.inr ht⟩)

theorem common {N B : Expr S} (h : Ω.HasType M A) (k : Ω.HasType N B) :
    ∃ n, PureTypeSystem.HasType P (Ω.context n) (M.rename (Expr.reverseIndex n))
      (A.rename (Expr.reverseIndex n)) ∧
      PureTypeSystem.HasType P (Ω.context n) (N.rename (Expr.reverseIndex n))
      (B.rename (Expr.reverseIndex n)) := by
  obtain ⟨n, ht⟩ := h
  obtain ⟨m, kt⟩ := k
  exact ⟨max n m, Ω.at_mono ht (le_max_left _ _), Ω.at_mono kt (le_max_right _ _)⟩

end HasType

theorem fresh_variable {A : Expr S} {s : S} (h : Ω.HasType A (.sort s)) (lower : Nat) :
    ∃ i, lower ≤ i ∧ Ω.HasType (.var i) A := by
  obtain ⟨n, ht⟩ := h
  have hA : A.Scoped n := by
    have hh := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at hh
  obtain ⟨m, hnm, hlm, he⟩ := Ω.saturated n A s ht lower
  have hAm := hA.mono hnm
  have hm : PureTypeSystem.HasType P (Ω.context m) (A.rename (Expr.reverseIndex m)) (.sort s) :=
    Ω.at_mono (A := .sort s) ht hnm
  refine ⟨m, hlm, m+1, ?_⟩
  rw [he, hAm.reverseIndex_succ]
  have hv := PureTypeSystem.HasType.var hm
  simpa only [Expr.rename, Expr.reverseIndex, Nat.lt_succ_self, ite_true,
    Nat.add_sub_cancel, Nat.sub_self] using hv

end ContextTower

namespace ContextTower.HasType

variable {S : Type u} {P : Specification S} {Ω : ContextTower P}
variable {M N A B : Expr S}

theorem application (hf : Ω.HasType M (.pi A B)) (ha : Ω.HasType N A) :
    Ω.HasType (.app M N) (B.instantiate N) := by
  obtain ⟨n, hf, ha⟩ := hf.common ha
  refine ⟨n, ?_⟩
  simpa only [Expr.rename, Expr.instantiate_rename] using
    PureTypeSystem.HasType.application hf ha

theorem conversion {s : S} (hM : Ω.HasType M A) (hB : Ω.HasType B (.sort s))
    (hc : Converts A B) : Ω.HasType M B := by
  obtain ⟨n, hM, hB⟩ := hM.common hB
  exact ⟨n, .conversion hM hB (hc.rename _)⟩

theorem subject_reduces (h : Ω.HasType M A) (hr : Reduces M N) : Ω.HasType N A := by
  obtain ⟨n, h⟩ := h
  exact ⟨n, h.subject_reduces (hr.rename _)⟩

theorem regularity (h : Ω.HasType M A) :
    (∃ s, A = .sort s) ∨ (∃ s, Ω.HasType A (.sort s)) := by
  obtain ⟨n, h⟩ := h
  obtain ⟨s, he⟩ | ⟨s, hs⟩ := h.regularity
  · left
    refine ⟨s, ?_⟩
    have he' := congrArg (Expr.rename (Expr.reverseIndex n)) he
    simpa only [Expr.reverseIndex_twice, Expr.rename] using he'
  · exact .inr ⟨s, n, hs⟩

theorem normalForm (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M.normalForm A :=
  h.subject_reduces (Expr.normalForm_spec (h.weaklyNormalizing hw)).1

theorem normalize_type (h : Ω.HasType M A) (hw : SystemWeaklyNormalizing P) :
    Ω.HasType M A.normalForm := by
  obtain ⟨s, rfl⟩ | ⟨s, hA⟩ := h.regularity
  · simpa only [Expr.normalForm_of_normal (Normal.sort s)] using h
  · exact .conversion h (hA.normalForm hw)
      (Expr.normalForm_spec (h.type_weaklyNormalizing hw)).1.converts

end ContextTower.HasType

/-! Finite generic contexts may have arbitrary raw actual images in the
saturated tower. Every such substitution is witnessed in one finite prefix;
no normalization or strong-normalization of the images is assumed. -/
namespace ContextTower
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

def TypedSubstitution (Γ : List (Expr S)) (σ : Nat → Expr S) : Prop :=
  ∀ n A, Lookup Γ n A → Ω.HasType (σ n) (A.subst σ)

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ : Nat → Expr S}

theorem tail {A : Expr S} (h : Ω.TypedSubstitution (A :: Γ) σ) :
    Ω.TypedSubstitution Γ (σ ∘ Nat.succ) := by
  intro n B hn
  have hh := h (n+1) (B.rename Nat.succ) (.succ A hn)
  simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- One common stage suffices for every declaration image, despite the
substitution being presented as a total function on indices. -/
theorem common_stage (h : Ω.TypedSubstitution Γ σ) :
    ∃ k, ∀ n A, Lookup Γ n A →
      PureTypeSystem.HasType P (Ω.context k) ((σ n).rename (Expr.reverseIndex k))
        ((A.subst σ).rename (Expr.reverseIndex k)) := by
  induction Γ generalizing σ with
  | nil => exact ⟨0, fun _ _ hn => nomatch hn⟩
  | cons B Γ ih =>
      obtain ⟨k, hk⟩ := ih h.tail
      obtain ⟨m, hm⟩ := h 0 (B.rename Nat.succ) (.zero B Γ)
      refine ⟨max k m, ?_⟩
      intro n A hn
      cases hn with
      | zero => exact Ω.at_mono hm (le_max_right k m)
      | succ B hn =>
          have hh := Ω.at_mono (hk _ _ hn) (le_max_left k m)
          simpa only [Expr.subst_rename, Function.comp_apply] using hh

/-- Extension assigns a raw term to the fresh generic binder. -/
theorem cons {A a : Expr S} (h : Ω.TypedSubstitution Γ σ)
    (ha : Ω.HasType a (A.subst σ)) : Ω.TypedSubstitution (A :: Γ) (fun n => match n with
      | 0 => a | n+1 => σ n) := by
  intro n B hn
  cases hn with
  | zero => simpa only [Expr.subst_rename, Function.comp_def] using ha
  | succ A hn => simpa only [Expr.subst_rename, Function.comp_def] using h _ _ hn
end TypedSubstitution

namespace HasType
variable {Ω} {Γ : List (Expr S)} {M A : Expr S} {σ : Nat → Expr S}

/-- Arbitrary typed substitution from a finite generic context to the tower. -/
theorem subst (h : PureTypeSystem.HasType P Γ M A) (hσ : Ω.TypedSubstitution Γ σ) :
    Ω.HasType (M.subst σ) (A.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  refine ⟨k, ?_⟩
  have hh := h.subst (Ω.valid k) (fun n => (σ n).rename (Expr.reverseIndex k)) (fun n B hn => by
    simpa only [← Expr.rename_subst] using hk n B hn)
  simpa only [← Expr.rename_subst] using hh
end HasType

namespace TypedSubstitution
variable {Ω} {Γ : List (Expr S)} {σ τ : Nat → Expr S}

theorem comp {Δ : List (Expr S)} (h : Ω.TypedSubstitution Δ τ)
    (hσ : PureTypeSystem.TypedSubstitution P Γ Δ σ) :
    Ω.TypedSubstitution Γ (fun n => (σ n).subst τ) := by
  intro n A hn
  simpa only [Expr.subst_subst] using HasType.subst (hσ n A hn) h

/-- The tower's finite-prefix identity environment uses global names. -/
theorem identity (n : Nat) : Ω.TypedSubstitution (Ω.context n) (.var ∘ Expr.reverseIndex n) := by
  intro i A hi
  have ht := PureTypeSystem.HasType.lookup (Ω.valid n) hi
  refine ⟨n, ?_⟩
  simpa only [Expr.subst_var_rename, Expr.rename, Function.comp_apply,
    Expr.reverseIndex_involutive n i, Expr.reverseIndex_twice] using ht
end TypedSubstitution

end ContextTower
end PureTypeSystem

end OAI
