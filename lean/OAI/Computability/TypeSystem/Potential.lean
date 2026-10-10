import OAI.Computability.TypeSystem.Profiles
import OAI.Computability.TypeSystem.Contexts

namespace OAI

/-! Profile paths and the no-expanding-neutral-leaf dependency. -/

namespace PureTypeSystem
universe u
namespace Profile
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem nonempty_of_sorted (hw : SystemWeaklyNormalizing P) {M : Expr S} {s : S}
    (h : HasType P Γ M (.sort s)) : (Profile P Γ M).Nonempty :=
  ⟨s, h.normalForm hw⟩

theorem context_head_conversion {A A' M : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hA' : HasType P Γ A' (.sort t))
    (hc : Converts A A') : Profile P (A :: Γ) M = Profile P (A' :: Γ) M := by
  ext r
  exact ⟨fun h => HasType.context_head_conversion h hA hA' hc,
    fun h => HasType.context_head_conversion h hA' hA (.symm _ _ hc)⟩

theorem inclusion_path {I J : Set S} (hI : FeasibleProfile P I)
    (hJ : FeasibleProfile P J) (h : J ⊆ I) : PositivePath (PrimaryEdge P) I J := by
  classical
  by_cases he : I = J
  · subst J; exact .refl
  · exact .single (.inclusion hI hJ (Set.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm he⟩))

theorem triple (hw : SystemWeaklyNormalizing P) {D E : Expr S} {s : S}
    (h : HasType P Γ (.pi D E) (.sort s)) :
    ProfileTriple P (Profile P Γ D) (Profile P (D :: Γ) E) (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have wD := hD.weaklyNormalizing hw
  have wE := hE.weaklyNormalizing hw
  have hD' := hD.normalForm hw
  have he : Profile P (D.normalForm :: Γ) E = Profile P (D :: Γ) E :=
    (context_head_conversion hD hD' (Expr.normalForm_spec wD).1.converts).symm
  refine ⟨feasible wD (nonempty_of_sorted hw hD),
    feasible wE (nonempty_of_sorted hw hE),
    feasible (h.weaklyNormalizing hw) (nonempty_of_sorted hw h), ?_⟩
  calc
    Profile P Γ (.pi D E) = Profile P Γ (.pi D.normalForm E.normalForm) := by
      rw [← Expr.normalForm_pi wD wE, Profile.normalForm]
    _ = OutProfile P (Profile P Γ D.normalForm)
        (Profile P (D.normalForm :: Γ) E.normalForm) :=
      pi (Expr.normalForm_spec wD).2 (Expr.normalForm_spec wE).2
    _ = OutProfile P (Profile P Γ D) (Profile P (D :: Γ) E) := by
      rw [Profile.normalForm, Profile.normalForm, he]

/-- The exact positive ascent from an instantiated codomain to its product.
It uses all sortings rather than choosing a functional specification. -/
theorem instantiate_product_path (hw : SystemWeaklyNormalizing P)
    {D E n : Expr S} {s : S} (h : HasType P Γ (.pi D E) (.sort s))
    (hn : HasType P Γ n D) :
    PositivePath (PrimaryEdge P) (Profile P Γ (E.instantiate n))
      (Profile P Γ (.pi D E)) := by
  obtain ⟨a, b, c, hD, hE, _, _⟩ := h.generation_pi
  have hout := hE.instantiate hn
  have hg := growth hw (hE.weaklyNormalizing hw) hn.valid _ (TypedSubstitution.single hn)
  have hp := inclusion_path
    (feasible (hout.weaklyNormalizing hw) (nonempty_of_sorted hw hout))
    (feasible (hE.weaklyNormalizing hw) (nonempty_of_sorted hw hE)) hg
  exact hp.trans (.single (.codomain (triple hw h)))
end Profile

namespace Expr
variable {S : Type u}
def head : Expr S → Expr S
  | .app f _ => head f
  | M => M
@[simp] theorem head_apps (M : Expr S) (ns : List (Expr S)) : (M.apps ns).head = M.head := by
  induction ns generalizing M with
  | nil => rfl
  | cons n ns ih => exact ih (.app M n)
end Expr

namespace HasType
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

/-- Reading a neutral spine backwards gives a positive path from the exact
result-type profile to the declaration-type profile of its head. -/
theorem neutral_profile_ascent (hw : SystemWeaklyNormalizing P)
    {M T : Expr S} (hn : Neutral M) (h : HasType P Γ M T) :
    ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
      PositivePath (PrimaryEdge P) (Profile P Γ T) (Profile P Γ D) := by
  induction hn generalizing T with
  | var n =>
      obtain ⟨D, hD, hc⟩ := h.generation
      refine ⟨n, D, rfl, hD, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.lookup h.valid hD).type_weaklyNormalizing hw) hc]
      exact .refl
  | @app f a hnf ih =>
      obtain ⟨D, E, hf, ha, hc⟩ := h.generation_app
      obtain ⟨s, hp⟩ := hf.product_type_sorted
      obtain ⟨n, A, hh, hl, hr⟩ := ih hf
      refine ⟨n, A, hh, hl, ?_⟩
      rw [Profile.converts (h.type_weaklyNormalizing hw)
        ((HasType.application hf ha).type_weaklyNormalizing hw) hc]
      exact (Profile.instantiate_product_path hw hp ha).trans hr

/-- This is the precise seed generated when a normal neutral type can be
changed at its head by substitution. The sort axiom is derived, not assumed. -/
theorem neutral_profile_seed (hw : SystemWeaklyNormalizing P)
    {M : Expr S} {s : S} (hn : Neutral M) (hM : Normal M)
    (h : HasType P Γ M (.sort s)) :
    Profile P Γ M = {s} ∧ (AxProfile P s).Nonempty ∧
      ∃ n D, M.head = .var n ∧ Lookup Γ n D ∧
        PositivePath (PrimaryEdge P) (AxProfile P s) (Profile P Γ D) := by
  refine ⟨Profile.neutral hM hn h, Profile.neutral_axiom hn h, ?_⟩
  simpa only [Profile.sort h.valid] using neutral_profile_ascent hw hn h
end HasType

namespace Neutral
variable {S : Type u} {M N : Expr S}

theorem rename (h : Neutral M) (ρ : Nat → Nat) : Neutral (M.rename ρ) := by
  induction h with
  | var n => exact .var _
  | app h ih => exact .app ih

theorem subst_of_head (h : Neutral M) (σ : Nat → Expr S)
    (hh : ∀ n, M.head = .var n → Neutral (σ n)) : Neutral (M.subst σ) := by
  induction h with
  | var n => exact hh n rfl
  | app h ih => exact .app (ih hh)

theorem beta (h : Neutral M) (hr : Beta M N) : Neutral N := by
  induction h generalizing N with
  | var n => cases hr
  | @app f a h ih =>
      cases hr with
      | app_left hr => exact .app (ih hr)
      | app_right _ => exact .app h
      | head => cases h

theorem reduces (h : Neutral M) (hr : Reduces M N) : Neutral N := by
  induction hr with
  | refl => exact h
  | tail _ hr ih => exact ih.beta hr

theorem normalForm (h : Neutral M) (hw : WeaklyNormalizing M) : Neutral M.normalForm :=
  h.reduces (Expr.normalForm_spec hw).1
end Neutral

/- A typed renaming preserves exact profiles of sorted types. The reverse
inclusion uses neutral uniqueness; it does not falsely assume functionality. -/
namespace Profile
variable {S : Type u} {P : Specification S}

theorem rename_normal {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n =>
      rw [neutral (hn.rename ρ) (.var _) (hT.rename hΔ ρ hρ), neutral hn (.var _) hT]
  | sort t =>
      exact (sort hΔ t).trans (sort hT.valid t).symm
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨D, E, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      rw [neutral (hn.rename ρ) (hneutral.rename ρ) (hT.rename hΔ ρ hρ),
        neutral hn hneutral hT]
  | lam A b ihA ihb => exact False.elim hT.lambda_cannot_have_sort_type
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n D, Lookup (A :: Γ) n D →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (D.rename (Expr.liftRen ρ)) := by
        intro n D hD
        cases hD with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hD =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hD) hA'
      rw [Expr.rename, pi (hn.pi_domain.rename ρ) (hn.pi_body.rename _), pi hn.pi_domain hn.pi_body,
        ihA hA hn.pi_domain hΔ ρ hρ,
        ihB hB hn.pi_body (.cons hΔ hA') _ hr]

theorem rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    Profile P Δ (T.rename ρ) = Profile P Γ T := by
  rw [← normalForm T, ← normalForm (T.rename ρ), Expr.normalForm_rename (hT.weaklyNormalizing hw) ρ]
  exact rename_normal (hT.normalForm hw) (Expr.normalForm_spec (hT.weaklyNormalizing hw)).2 hΔ ρ hρ

theorem weaken (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T D : Expr S} {s t : S} (hT : HasType P Γ T (.sort s))
    (hD : HasType P Γ D (.sort t)) :
    Profile P (D :: Γ) (T.rename Nat.succ) = Profile P Γ T :=
  rename hw hT (.cons hD.valid hD) Nat.succ
    (fun _ _ hn => .weaken (HasType.lookup hD.valid hn) hD)
end Profile

/-- Every image which can replace a neutral head originates at the chosen
outer binder profile. Ordinary one-variable substitution, and every lifting
of it through additional binders, have this property. -/
def SingleSource {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (σ : Nat → Expr S) (I : Set S) : Prop :=
  ∀ n D, Lookup Γ n D → ¬ Neutral (σ n) → Profile P Γ D = I

namespace SingleSource
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {σ : Nat → Expr S} {I : Set S}

theorem single (hw : SystemWeaklyNormalizing P) {D q : Expr S} {s : S}
    (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.single q) (Profile P Γ D) := by
  intro n A hn hbad
  cases hn with
  | zero => exact Profile.weaken hw hD hD
  | succ _ _ => exact False.elim (hbad (.var _))

theorem lift (hw : SystemWeaklyNormalizing P) (h : SingleSource P Γ σ I)
    {D : Expr S} {s : S} (hD : HasType P Γ D (.sort s)) :
    SingleSource P (D :: Γ) (Expr.liftSub σ) I := by
  intro n A hn hbad
  cases hn with
  | zero => exact False.elim (hbad (.var 0))
  | succ _ hn =>
      obtain ⟨t, hA⟩ := HasType.lookup_sorted hD.valid hn
      rw [Profile.weaken hw hA hD]
      exact h _ _ hn (fun hh => hbad (hh.rename Nat.succ))
end SingleSource

namespace ForbiddenConfiguration
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- The source's critical neutral-leaf argument. No beta-normal neutral leaf
in this component can become a product under substitution of the outer
binder: doing so would produce exactly the excluded graph configuration. -/
theorem of_neutral_expansion (hw : SystemWeaklyNormalizing P)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {M A B : Expr S} {s : S} (h : HasType P Γ M (.sort s))
    (hn : Normal M) (hne : Neutral M) (hM : Profile P Γ M ∈ D)
    (he : (M.subst σ).normalForm = .pi A B) : ForbiddenConfiguration P C := by
  obtain ⟨hp, hax, n, F, hh, hf, hpath⟩ := h.neutral_profile_seed hw hne hn
  have hbad : ¬ Neutral (σ n) := by
    intro hs
    have hM' := hne.subst_of_head σ (by
      intro m hm
      have heq : m = n := by simpa only [hh, Expr.var.injEq] using hm.symm
      exact heq.symm ▸ hs)
    have hnorm := hM'.normalForm ((h.subst hΔ σ hσ).weaklyNormalizing hw)
    rw [he] at hnorm
    cases hnorm
  have hF := hsrc n F hf hbad
  rw [hF] at hpath
  exact ⟨D, hD, hplain, hneg, I, J, K, s, htr, hJ, hK, hp ▸ hM, hax, hpath⟩
end ForbiddenConfiguration

namespace ObservationLayers
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}
theorem positive (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    J ∈ ObservationLayers P C := by
  obtain ⟨s, hs, hax, hpath⟩ := h
  exact ⟨s, hs, hax, hpath.trans hp⟩

theorem secondary (h : I ∈ ObservationLayers P C) (hp : PositivePath (PrimaryEdge P) I J) :
    PositivePath (SecondaryEdge P C) I J := by
  induction hp with
  | refl => exact .refl
  | @tail J K hp he ih =>
      exact .tail ih (.positive (positive h hp) (positive h (.tail hp he)) he)
end ObservationLayers

namespace ActiveLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem layer (h : ActiveLayer P C I) : I ∈ ObservationLayers P C := by
  obtain ⟨D, hD, b, hp⟩ := h
  cases hp with
  | nil => exact hD.1
  | cons he _ => cases he with
    | positive hI _ _ => exact hI
    | negative hI _ _ _ => exact hI

theorem predecessor (h : ActiveLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    ActiveLayer P C I := by
  obtain ⟨D, hD, hr⟩ := h
  exact ⟨D, hD, hp.trans hr⟩
end ActiveLayer

namespace IsComponent
variable {S : Type u} {P : Specification S} {C D : Set (Set S)}

/-- Interpolation of a counted post-substitution codomain through the
original product triple. -/
theorem codomain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    {I J K J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D) (hJ' : J' ∈ D)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) : J ∈ D := by
  have hJH := ObservationLayers.positive (hl J' hJ') hJJ'
  exact hD.between hJ' hK (ObservationLayers.secondary (hl J' hJ') hJJ').reach
    (Reach.single (.positive hJH (hl K hK) (.codomain htr)))

/-- Domain interpolation also needs the post open codomain to be active;
this is exactly the side condition in the source potential, not a stronger
assumption that every domain dependency is retained. -/
theorem domain_interpolation (hD : IsComponent (SecondaryEdge P C) D)
    (hl : ∀ X ∈ D, X ∈ ObservationLayers P C)
    (ha : ∀ X ∈ D, ActiveLayer P C X)
    {I J K I' J' : Set S} (htr : ProfileTriple P I J K) (hK : K ∈ D)
    (hI' : I' ∈ D) (hJ' : ActiveLayer P C J')
    (hII' : PositivePath (PrimaryEdge P) I' I)
    (hJJ' : PositivePath (PrimaryEdge P) J' J) :
    I ∈ D ∧ ActiveLayer P C J := by
  have hIH := ObservationLayers.positive (hl I' hI') hII'
  have hJH := ObservationLayers.positive hJ'.layer hJJ'
  have hKH := hl K hK
  exact ⟨hD.between hI' hK (ObservationLayers.secondary (hl I' hI') hII').reach
    (Reach.single (.negative hIH hJH hKH htr)),
    (ha K hK).predecessor (Reach.single (.positive hJH hKH (.codomain htr)))⟩
end IsComponent

namespace Profile
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem growth_path (hw : SystemWeaklyNormalizing P) {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) :
    PositivePath (PrimaryEdge P) (Profile P Δ (T.subst σ)) (Profile P Γ T) := by
  have ht := hT.subst hΔ σ hσ
  exact inclusion_path (feasible (ht.weaklyNormalizing hw) (nonempty_of_sorted hw ht))
    (feasible (hT.weaklyNormalizing hw) (nonempty_of_sorted hw hT))
    (growth hw (hT.weaklyNormalizing hw) hΔ σ hσ)
end Profile

/-- Context conversion as exact equality of all judgments on unchanged
syntax. Both contexts are required valid. This auxiliary relation carries
no semantic or normalization assumption. -/
structure ContextEquivalent {S : Type u} (P : Specification S)
    (Γ Δ : List (Expr S)) : Prop where
  valid_left : ValidContext P Γ
  valid_right : ValidContext P Δ
  typing : ∀ (M A : Expr S), HasType P Γ M A ↔ HasType P Δ M A

namespace ContextEquivalent
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem symm (h : ContextEquivalent P Γ Δ) : ContextEquivalent P Δ Γ :=
  ⟨h.valid_right, h.valid_left, fun _ _ => (h.typing _ _).symm⟩

theorem profile (h : ContextEquivalent P Γ Δ) (M : Expr S) :
    Profile P Γ M = Profile P Δ M := by
  ext s
  exact h.typing _ _

theorem cons (h : ContextEquivalent P Γ Δ) {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) : ContextEquivalent P (A :: Γ) (A :: Δ) := by
  have lift_dir {Γ Δ : List (Expr S)} (h : ContextEquivalent P Γ Δ)
      (hA : HasType P Γ A (.sort s)) :
      ∀ M B, HasType P (A :: Γ) M B → HasType P (A :: Δ) M B := by
    intro M B ht
    have hA' := (h.typing _ _).1 hA
    have hs : TypedSubstitution P (A :: Γ) (A :: Δ) Expr.var := by
      intro n D hn
      rw [Expr.subst_var]
      cases hn with
      | zero => exact .var hA'
      | succ _ hn => exact .weaken ((h.typing _ _).1 (HasType.lookup h.valid_left hn)) hA'
    simpa only [Expr.subst_var] using ht.subst (.cons h.valid_right hA') _ hs
  have hA' := (h.typing _ _).1 hA
  exact ⟨.cons h.valid_left hA, .cons h.valid_right hA',
    fun M B => ⟨lift_dir h hA M B, lift_dir h.symm hA' M B⟩⟩

theorem head_conversion {A B : Expr S} {s t : S}
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hc : Converts A B) : ContextEquivalent P (A :: Γ) (B :: Γ) :=
  ⟨.cons hA.valid hA, .cons hB.valid hB, fun _ _ =>
    ⟨fun h => h.context_head_conversion hA hB hc,
      fun h => h.context_head_conversion hB hA (.symm _ _ hc)⟩⟩
end ContextEquivalent

namespace PlainObservations
open Classical
variable {S : Type u}
/-- The exact source syntax-tree potential. Its recursive child conditions
retain the active-open-codomain guard on a counted domain. -/
noncomputable def potential (P : Specification S) (C D : Set (Set S))
    (Γ : List (Expr S)) : Expr S → Nat
  | .pi A B => by
      classical
      exact 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B else 0)
  | _ => 1

variable {P : Specification S} {C D : Set (Set S)}

theorem potential_context {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (h : ContextEquivalent P Γ Δ) :
    potential P C D Γ T = potential P C D Δ T := by
  induction T generalizing Γ Δ s with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      simp only [potential]
      rw [h.profile A, (h.cons hA).profile B, ihA hA h, ihB hB (h.cons hA)]

/-- Normalizing a product does not change the contexts in which its child
contributions are measured: raw and normalized annotations are context
convertible. This keeps the dependent codomain count honest. -/
theorem potential_normalized_pi (hw : SystemWeaklyNormalizing P)
    {Γ : List (Expr S)} {A B : Expr S} {s : S}
    (h : HasType P Γ (.pi A B) (.sort s)) :
    potential P C D Γ (Expr.pi A B).normalForm = 1 +
      (if Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B)
       then potential P C D Γ A.normalForm else 0) +
      (if Profile P (A :: Γ) B ∈ D then potential P C D (A :: Γ) B.normalForm else 0) := by
  classical
  obtain ⟨a, b, c, hA, hB, _, _⟩ := h.generation_pi
  have wA := hA.weaklyNormalizing hw
  have wB := hB.weaklyNormalizing hw
  have hc := ContextEquivalent.head_conversion hA (hA.normalForm hw) (Expr.normalForm_spec wA).1.converts
  have hp := (potential_context (C := C) (D := D) (hB.normalForm hw) hc).symm
  rw [Expr.normalForm_pi wA wB, potential, ← hc.profile B.normalForm, hp,
    Profile.normalForm, Profile.normalForm]

/-- The full potential inequality. The outer triple and its codomain/product
vertices are fixed exactly as in the source legal-frame argument. SingleSource
is proved above for the actual one-variable substitution and all binder lifts. -/
theorem potential_subst_le (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {I J K : Set S} (htr : ProfileTriple P I J K) (hJ : J ∈ D) (hK : K ∈ D)
    {Γ Δ : List (Expr S)} (hΔ : ValidContext P Δ) {σ : Nat → Expr S}
    (hσ : TypedSubstitution P Γ Δ σ) (hsrc : SingleSource P Γ σ I)
    {T : Expr S} {s : S} (hT : HasType P Γ T (.sort s)) (hn : Normal T)
    (hTC : Profile P Γ T ∈ D) :
    potential P C D Δ (T.subst σ).normalForm ≤ potential P C D Γ T := by
  classical
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  have leaf {Γ Δ : List (Expr S)} {σ : Nat → Expr S} {M : Expr S} {s : S}
      (hΔ : ValidContext P Δ) (hσ : TypedSubstitution P Γ Δ σ)
      (hsrc : SingleSource P Γ σ I) (hM : HasType P Γ M (.sort s))
      (hn : Normal M) (hne : Neutral M) (hMC : Profile P Γ M ∈ D) :
      potential P C D Δ (M.subst σ).normalForm = 1 := by
    cases he : (M.subst σ).normalForm with
    | pi A B =>
        exact False.elim (hno (ForbiddenConfiguration.of_neutral_expansion hw hD hplain hneg
          htr hJ hK hΔ hσ hsrc hM hn hne hMC he))
    | var n | sort t | app f a | lam A b => rfl
  induction T generalizing Γ Δ σ s with
  | var n => exact le_of_eq (leaf hΔ hσ hsrc hT hn (.var n) hTC)
  | sort t => simp only [Expr.subst, Expr.normalForm_of_normal (Normal.sort t), potential, le_refl]
  | lam A b => exact False.elim hT.lambda_cannot_have_sort_type
  | app f a ihf iha =>
      have hneutral : Neutral (.app f a) := by
        obtain ⟨t, he⟩ | h | ⟨A, B, he⟩ := hT.sorted_normal_shape hn
        · cases he
        · exact h
        · cases he
      exact le_of_eq (leaf hΔ hσ hsrc hT hn hneutral hTC)
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.subst hΔ σ hσ
      have hΔ' : ValidContext P (A.subst σ :: Δ) := .cons hΔ hA'
      have hσ' := hσ.lift hA'
      have hB' := hB.subst hΔ' _ hσ'
      have htr' := Profile.triple hw hT
      have hAp := Profile.growth_path hw hA hΔ σ hσ
      have hBp := Profile.growth_path hw hB hΔ' _ hσ'
      rw [Expr.subst, potential_normalized_pi hw (hT.subst hΔ σ hσ), potential]
      apply Nat.add_le_add
      · apply Nat.add_le_add_left
        split_ifs with hc hc'
        · exact ihA hΔ hσ hsrc hA hn.pi_domain hc'.1
        · obtain ⟨hAC, hBa⟩ := hD.domain_interpolation hl ha htr' hTC hc.1 hc.2 hAp hBp
          exact False.elim (hc' ⟨hAC, hBa⟩)
        · exact Nat.zero_le _
        · exact le_rfl
      · split_ifs with hc hc'
        · exact ihB hΔ' hσ' (hsrc.lift hw hA) hB hn.pi_body hc'
        · exact False.elim (hc' (hD.codomain_interpolation hl htr' hTC hc hBp))
        · exact Nat.zero_le _
        · exact le_rfl

theorem potential_pos (Γ : List (Expr S)) (T : Expr S) : 0 < potential P C D Γ T := by
  cases T <;> simp only [potential] <;> omega

/-- Exact legal-frame potential drop in the negative plain component,
including the strict syntactic-child inequality. -/
theorem frame_potential_drop (hw : SystemWeaklyNormalizing P)
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {Γ : List (Expr S)} {A B n : Expr S} {s : S}
    (hT : HasType P Γ (.pi A B) (.sort s)) (hnT : Normal (.pi A B))
    (hn : HasType P Γ n A) (hK : Profile P Γ (.pi A B) ∈ D)
    (hL : Profile P Γ (B.instantiate n) ∈ D) :
    potential P C D Γ (B.instantiate n).normalForm ≤ potential P C D (A :: Γ) B ∧
      potential P C D (A :: Γ) B < potential P C D Γ (.pi A B) := by
  have ha : ∀ X ∈ D, ActiveLayer P C X := fun X hX => (hplain X hX).active
  have hl : ∀ X ∈ D, X ∈ ObservationLayers P C := fun X hX => (ha X hX).layer
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hn.valid _ (TypedSubstitution.single hn)
  have hJ := hD.codomain_interpolation hl htr hK hL hp
  refine ⟨potential_subst_le hw hno hD hplain hneg htr hJ hK hn.valid
    (TypedSubstitution.single hn) (SingleSource.single hw hA) hB hnT.pi_body hJ, ?_⟩
  simp only [potential, ite_eq_left hJ]
  omega

theorem frame_domain_drop (hplain : ∀ I ∈ D, PlainLayer P C I)
    {Γ : List (Expr S)} {A B : Expr S}
    (hI : Profile P Γ A ∈ D) (hJ : Profile P (A :: Γ) B ∈ D) :
    potential P C D Γ A < potential P C D Γ (.pi A B) := by
  have hc : Profile P Γ A ∈ D ∧ ActiveLayer P C (Profile P (A :: Γ) B) :=
    ⟨hI, (hplain _ hJ).active⟩
  simp only [potential, ite_eq_left hc, ite_eq_left hJ]
  omega

/-- The potential counts positions, so valid thinning does not change it.
The equality is exact also under every dependent binder. -/
theorem potential_rename (hw : SystemWeaklyNormalizing P)
    {Γ Δ : List (Expr S)} {T : Expr S} {s : S}
    (hT : HasType P Γ T (.sort s)) (hΔ : ValidContext P Δ) (ρ : Nat → Nat)
    (hρ : ∀ n B, Lookup Γ n B → HasType P Δ (.var (ρ n)) (B.rename ρ)) :
    potential P C D Δ (T.rename ρ) = potential P C D Γ T := by
  induction T generalizing Γ Δ s ρ with
  | var n | sort t | app f a | lam A b => rfl
  | pi A B ihA ihB =>
      obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
      have hA' := hA.rename hΔ ρ hρ
      have hr : ∀ n E, Lookup (A :: Γ) n E →
          HasType P (A.rename ρ :: Δ) (.var (Expr.liftRen ρ n))
            (E.rename (Expr.liftRen ρ)) := by
        intro n E hE
        cases hE with
        | zero =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def] using HasType.var hA'
        | succ _ hE =>
            simpa only [Expr.liftRen, Expr.rename_comp, Function.comp_def, Expr.rename] using
              HasType.weaken (hρ _ _ hE) hA'
      simp only [Expr.rename, potential]
      rw [Profile.rename hw hA hΔ ρ hρ,
        Profile.rename hw hB (.cons hΔ hA') _ hr,
        ihA hA hΔ ρ hρ, ihB hB (.cons hΔ hA') _ hr]

end PlainObservations

namespace ContextTower

section
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- The source profile on syntax with fixed global variable names. -/
def profile (T : Expr S) : Set S := {s | Ω.HasType T.normalForm (.sort s)}

variable (hw : SystemWeaklyNormalizing P)
include hw

theorem profile_at_next {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Profile P (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨D, t, hD, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact Profile.weaken hw ht hD

theorem profile_at_mono {n m : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    Profile P (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih => exact (Ω.profile_at_next hw (Ω.at_mono (A := .sort s) ht h)).trans ih

/-- A single available sorting fixes the exact profile at every later
prefix. Extra sorting rules cannot appear merely by weakening. -/
theorem profile_at {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.profile T = Profile P (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have w : WeaklyNormalizing T := (show Ω.HasType T (.sort s) from ⟨n, ht⟩).weaklyNormalizing hw
  ext t
  constructor
  · rintro ⟨m, hm⟩
    have hn := Ω.at_mono (A := .sort t) hm (le_max_left m n)
    change PureTypeSystem.HasType P (Ω.context (max m n))
      (T.normalForm.rename (Expr.reverseIndex (max m n))) (.sort t) at hn
    rw [← Expr.normalForm_rename w] at hn
    have he := Ω.profile_at_mono hw ht (le_max_right m n)
    exact he ▸ hn
  · intro hn
    refine ⟨n, ?_⟩
    change PureTypeSystem.HasType P (Ω.context n) (T.normalForm.rename (Expr.reverseIndex n)) (.sort t)
    rw [← Expr.normalForm_rename w]
    exact hn

omit hw in
theorem profile_normalForm (T : Expr S) : Ω.profile T.normalForm = Ω.profile T := by
  simp only [profile, Expr.normalForm_idem]

theorem profile_nonempty {T : Expr S} {s : S} (ht : Ω.HasType T (.sort s)) :
    (Ω.profile T).Nonempty := ⟨s, ht.normalForm hw⟩

theorem profile_feasible {T : Expr S} {s : S} (ht : Ω.HasType T (.sort s)) :
    FeasibleProfile P (Ω.profile T) := by
  obtain ⟨n, hn⟩ := ht
  change PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s) at hn
  rw [Ω.profile_at hw hn]
  exact Profile.feasible (hn.weaklyNormalizing hw) (Profile.nonempty_of_sorted hw hn)

theorem potential_at_next (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    PlainObservations.potential P C D (Ω.context (n+1)) (T.rename (Expr.reverseIndex (n+1))) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have hs : T.Scoped n := by
    have h := ht.scope.1.reverseIndex
    rwa [Ω.length, Expr.reverseIndex_twice] at h
  obtain ⟨A, t, hA, he⟩ := Ω.step n
  rw [he, hs.reverseIndex_succ]
  exact PlainObservations.potential_rename hw ht (.cons hA.valid hA) Nat.succ
    (fun _ _ hn => .weaken (PureTypeSystem.HasType.lookup hA.valid hn) hA)

theorem potential_at_mono (C D : Set (Set S)) {n m : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s))
    (h : n ≤ m) :
    PlainObservations.potential P C D (Ω.context m) (T.rename (Expr.reverseIndex m)) =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  induction h with
  | refl => rfl
  | @step m h ih =>
      exact (Ω.potential_at_next hw C D (Ω.at_mono (A := .sort s) ht h)).trans ih

noncomputable def potential (C D : Set (Set S)) (T : Expr S) : Nat :=
  if h : ∃ n s, PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)
  then PlainObservations.potential P C D (Ω.context h.choose) (T.rename (Expr.reverseIndex h.choose))
  else 1

theorem potential_at (C D : Set (Set S)) {n : Nat} {T : Expr S} {s : S}
    (ht : PureTypeSystem.HasType P (Ω.context n) (T.rename (Expr.reverseIndex n)) (.sort s)) :
    Ω.potential C D T =
      PlainObservations.potential P C D (Ω.context n) (T.rename (Expr.reverseIndex n)) := by
  have h : ∃ m t, PureTypeSystem.HasType P (Ω.context m) (T.rename (Expr.reverseIndex m)) (.sort t) :=
    ⟨n, s, ht⟩
  rw [potential, dite_eq_left h]
  obtain ⟨t, hT⟩ := h.choose_spec
  exact (Ω.potential_at_mono hw C D hT (le_max_left h.choose n)).symm.trans
    (Ω.potential_at_mono hw C D ht (le_max_right h.choose n))

/-- Formation data for a global legal frame, retaining the open codomain
profile instead of imposing functionality. -/
theorem frame_profiles {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ J, ProfileTriple P (Ω.profile A) J (Ω.profile (.pi A B)) ∧
      PositivePath (PrimaryEdge P) (Ω.profile (B.instantiate q)) J := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have htr := Profile.triple hw hT
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename] at hp
  refine ⟨Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
    (B.rename (Expr.liftRen (Expr.reverseIndex n))), ?_, ?_⟩
  · rw [Ω.profile_at hw hA, Ω.profile_at hw (T := .pi A B) hT]
    exact htr
  · rw [Ω.profile_at hw hQ]
    exact hp

omit hw in
theorem domain_sorted {A B : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) : ∃ a, Ω.HasType A (.sort a) := by
  obtain ⟨n, hT⟩ := hT
  obtain ⟨a, b, c, hA, _, _, _⟩ := hT.generation_pi
  exact ⟨a, n, hA⟩

omit hw in
theorem frame_target_sorted {A B q : Expr S} {s : S}
    (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A) :
    ∃ b, Ω.HasType (B.instantiate q) (.sort b) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  obtain ⟨a, b, c, _, hB, _, _⟩ := hT.generation_pi
  refine ⟨b, n, ?_⟩
  have h := hB.instantiate hq
  change PureTypeSystem.HasType P (Ω.context n)
    ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate (q.rename (Expr.reverseIndex n)))
    (.sort b) at h
  rw [Expr.instantiate_rename] at h
  exact h

/-- Global form of the source strict target-potential inequality. -/
theorem frame_target_drop {C D : Set (Set S)}
    (hno : ¬ ForbiddenConfiguration P C)
    (hD : IsComponent (SecondaryEdge P C) D) (hplain : ∀ I ∈ D, PlainLayer P C I)
    (hneg : ∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true)
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s))
    (hN : Normal (.pi A B)) (hq : Ω.HasType q A)
    (hK : Ω.profile (.pi A B) ∈ D) (hL : Ω.profile (B.instantiate q) ∈ D) :
    Ω.potential C D (B.instantiate q).normalForm < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have wQ : WeaklyNormalizing (B.instantiate q) :=
    (show Ω.HasType (B.instantiate q) (.sort b) from ⟨n, hQ⟩).weaklyNormalizing hw
  have hQN := hQ.normalForm hw
  rw [Expr.normalForm_rename wQ] at hQN
  rw [Ω.potential_at hw C D hQN, Ω.potential_at hw C D (T := .pi A B) hT,
    ← Expr.normalForm_rename wQ, ← Expr.instantiate_rename]
  rw [Ω.profile_at hw (T := .pi A B) hT] at hK
  rw [Ω.profile_at hw hQ, ← Expr.instantiate_rename] at hL
  have hh := PlainObservations.frame_potential_drop hw hno hD hplain hneg hT
    (hN.rename _) hq hK hL
  exact lt_of_le_of_lt hh.1 hh.2

/-- Every active same-component domain is counted, even when a frame exits
its component. This is why the potential's guard is activity, not membership
of the open codomain in the component. -/
theorem frame_domain_drop {C D : Set (Set S)}
    {A B q : Expr S} {s : S} (hT : Ω.HasType (.pi A B) (.sort s)) (hq : Ω.HasType q A)
    (hK : ActiveLayer P C (Ω.profile (.pi A B)))
    (hL : ActiveLayer P C (Ω.profile (B.instantiate q)))
    (hI : Ω.profile A ∈ D) :
    Ω.potential C D A < Ω.potential C D (.pi A B) := by
  obtain ⟨n, hT, hq⟩ := hT.common hq
  change PureTypeSystem.HasType P (Ω.context n)
    (.pi (A.rename (Expr.reverseIndex n)) (B.rename (Expr.liftRen (Expr.reverseIndex n)))) (.sort s) at hT
  obtain ⟨a, b, c, hA, hB, _, _⟩ := hT.generation_pi
  have hQ := hB.instantiate hq
  rw [Expr.instantiate_rename] at hQ
  have hp := Profile.growth_path hw hB hq.valid _ (TypedSubstitution.single hq)
  change PositivePath (PrimaryEdge P)
    (Profile P (Ω.context n) ((B.rename (Expr.liftRen (Expr.reverseIndex n))).instantiate
      (q.rename (Expr.reverseIndex n)))) _ at hp
  rw [Expr.instantiate_rename, ← Ω.profile_at hw hQ] at hp
  have hJH := ObservationLayers.positive hL.layer hp
  have hJ := hK.predecessor (Reach.single (SecondaryEdge.positive hJH hK.layer
    (by rw [Ω.profile_at hw (T := .pi A B) hT]; exact .codomain (Profile.triple hw hT))))
  have hc : Profile P (Ω.context n) (A.rename (Expr.reverseIndex n)) ∈ D ∧
      ActiveLayer P C (Profile P (A.rename (Expr.reverseIndex n) :: Ω.context n)
        (B.rename (Expr.liftRen (Expr.reverseIndex n)))) := by
    exact ⟨Ω.profile_at hw hA ▸ hI, hJ⟩
  rw [Ω.potential_at hw C D hA, Ω.potential_at hw C D (T := .pi A B) hT]
  simp only [Expr.rename, PlainObservations.potential, ite_eq_left hc]
  omega

end

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Substitution of a typed normal generic expression can only grow its exact
profile. The common-stage reduction keeps nonfunctional sort choices. -/
theorem profile_subst_growth (hw : SystemWeaklyNormalizing P) {Γ : List (Expr S)}
    {T : Expr S} {s : S} {σ : Nat → Expr S} (ht : PureTypeSystem.HasType P Γ T (.sort s))
    (hσ : Ω.TypedSubstitution Γ σ) : Profile P Γ T ⊆ Ω.profile (T.subst σ) := by
  obtain ⟨k, hk⟩ := TypedSubstitution.common_stage hσ
  let σ' := fun n => (σ n).rename (Expr.reverseIndex k)
  have hs : PureTypeSystem.TypedSubstitution P Γ (Ω.context k) σ' := by
    intro n A hn
    simpa only [σ', ← Expr.rename_subst] using hk n A hn
  have hT := ht.subst (Ω.valid k) σ' hs
  have hp := Profile.growth hw (ht.weaklyNormalizing hw) (Ω.valid k) σ' hs
  have he : T.subst σ' = (T.subst σ).rename (Expr.reverseIndex k) := (Expr.rename_subst _ _ _).symm
  rw [he] at hT hp
  rwa [Ω.profile_at hw hT]

end ContextTower
end PureTypeSystem

end OAI
