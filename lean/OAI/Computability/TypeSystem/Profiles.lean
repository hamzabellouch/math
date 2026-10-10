import OAI.Computability.TypeSystem.Typing

namespace OAI

namespace PureTypeSystem

universe u

/-- Sorts assigned to the full normal form. -/
def Profile {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (T : Expr S) : Set S := {s | HasType P Γ T.normalForm (.sort s)}

def AxProfile {S : Type u} (P : Specification S) (s : S) : Set S :=
  {t | P.axioms s t}

def OutProfile {S : Type u} (P : Specification S) (I J : Set S) : Set S :=
  {c | ∃ a ∈ I, ∃ b ∈ J, P.rule a b c}

/-- Semantic feasible profiles. Normal witnesses are retained, rather than
assuming the manuscript's characterization of this finite set. -/
def FeasibleProfile {S : Type u} (P : Specification S) (I : Set S) : Prop :=
  I.Nonempty ∧ ∃ Γ T, ValidContext P Γ ∧ Normal T ∧ Profile P Γ T = I

structure ProfileTriple {S : Type u} (P : Specification S) (I J K : Set S) : Prop where
  domain : FeasibleProfile P I
  codomain : FeasibleProfile P J
  product : FeasibleProfile P K
  output : K = OutProfile P I J

/-- The sign is true for a domain edge and false for a positive edge. -/
inductive PrimaryEdge {S : Type u} (P : Specification S) :
    Set S → Set S → Bool → Prop
  | inclusion {I J} : FeasibleProfile P I → FeasibleProfile P J →
      J ⊂ I → PrimaryEdge P I J false
  | domain {I J K} : ProfileTriple P I J K → PrimaryEdge P I K true
  | codomain {I J K} : ProfileTriple P I J K → PrimaryEdge P J K false

/-- Finite directed walks, with repeated edges permitted and parity retained. -/
inductive SignedPath {V : Type*} (E : V → V → Bool → Prop) : V → V → Bool → Prop
  | nil (v) : SignedPath E v v false
  | cons {u v w p q} : E u v p → SignedPath E v w q →
      SignedPath E u w (Bool.xor p q)

def Reach {V : Type*} (E : V → V → Bool → Prop) (v w : V) : Prop :=
  ∃ b, SignedPath E v w b

def PositivePath {V : Type*} (E : V → V → Bool → Prop) : V → V → Prop :=
  Relation.ReflTransGen (fun v w => E v w false)

/-- A full strongly connected component, not merely a connected subset. -/
def IsComponent {V : Type*} (E : V → V → Bool → Prop) (C : Set V) : Prop :=
  ∃ r ∈ C, ∀ v, v ∈ C ↔ Reach E r v ∧ Reach E v r

namespace SignedPath

variable {V : Type*} {E : V → V → Bool → Prop}

theorem singleton {v w : V} {p : Bool} (h : E v w p) : SignedPath E v w p := by
  simpa only [Bool.xor_false] using SignedPath.cons h (.nil w)

theorem append {v w z : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E w z q) :
    SignedPath E v z (Bool.xor p q) := by
  induction h with
  | nil v => simpa using k
  | cons he ht ih => simpa only [Bool.xor_assoc] using SignedPath.cons he (ih k)

theorem parity_unique {v w : V} {p q : Bool}
    (h : SignedPath E v w p) (k : SignedPath E v w q)
    (hr : Reach E w v) (hodd : ¬ SignedPath E v v true) : p = q := by
  obtain ⟨r, hr⟩ := hr
  have hpr := h.append hr
  have hqr := k.append hr
  cases p <;> cases q <;> cases r <;> simp_all

end SignedPath

namespace Reach

variable {V : Type*} {E : V → V → Bool → Prop} {v w z : V}

theorem refl (v : V) : Reach E v v := ⟨false, .nil v⟩

theorem trans (h : Reach E v w) (k : Reach E w z) : Reach E v z := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := k
  exact ⟨_, hp.append hq⟩

theorem single {p : Bool} (h : E v w p) : Reach E v w := ⟨p, .singleton h⟩

end Reach

namespace PositivePath

variable {V : Type*} {E : V → V → Bool → Prop} {v w : V}

theorem parity (h : PositivePath E v w) : SignedPath E v w false := by
  induction h with
  | refl => exact .nil _
  | tail _ he ih => exact ih.append (.singleton he)

theorem reach (h : PositivePath E v w) : Reach E v w := ⟨false, h.parity⟩

end PositivePath

namespace IsComponent

variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V} {v w z : V}

theorem connected (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C) : Reach E v w := by
  obtain ⟨r, hr, hc⟩ := h
  exact ((hc v).1 hv).2.trans ((hc w).1 hw).1

theorem between (h : IsComponent E C) (hv : v ∈ C) (hw : w ∈ C)
    (hvz : Reach E v z) (hzw : Reach E z w) : z ∈ C := by
  obtain ⟨r, hr, hc⟩ := h
  exact (hc z).2 ⟨((hc v).1 hv).1.trans hvz, hzw.trans ((hc w).1 hw).2⟩

end IsComponent

/-- Positive closure of the sort-profile seeds. -/
def ObservationLayers {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set (Set S) := {I | ∃ s, {s} ∈ C ∧ (AxProfile P s).Nonempty ∧
      PositivePath (PrimaryEdge P) (AxProfile P s) I}

inductive SecondaryEdge {S : Type u} (P : Specification S) (C : Set (Set S)) :
    Set S → Set S → Bool → Prop
  | positive {I J} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      PrimaryEdge P I J false → SecondaryEdge P C I J false
  | negative {I J K} : I ∈ ObservationLayers P C → J ∈ ObservationLayers P C →
      K ∈ ObservationLayers P C → ProfileTriple P I J K →
      SecondaryEdge P C I K true

def DirectLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := I ∈ ObservationLayers P C ∧
      ∃ J ∈ C, ∃ K ∈ C, ProfileTriple P I J K

def ActiveLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop := ∃ D, DirectLayer P C D ∧ Reach (SecondaryEdge P C) I D

def PlainLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) : Prop :=
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D false) ∧
  (∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D true)

def FreeLayer {S : Type u} (P : Specification S) (C : Set (Set S))
    (I : Set S) (sign : Bool) : Prop := ¬ PlainLayer P C I ∧
      ∃ D, DirectLayer P C D ∧ SignedPath (SecondaryEdge P C) I D sign

/-- The finite-graph obstruction excluded by system-wide weak normalization.
It is not an extra hypothesis on the normalization theorem. -/

def ForbiddenConfiguration {S : Type u} (P : Specification S) (C : Set (Set S)) : Prop :=
  ∃ D : Set (Set S), IsComponent (SecondaryEdge P C) D ∧
    (∀ I ∈ D, PlainLayer P C I) ∧
    (∃ I ∈ D, ∃ K ∈ D, SecondaryEdge P C I K true) ∧
    ∃ I J K s, ProfileTriple P I J K ∧ J ∈ D ∧ K ∈ D ∧ {s} ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PrimaryEdge P) (AxProfile P s) I

namespace PlainLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active (h : PlainLayer P C I) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.1
  exact ⟨D, hD, false, hp⟩

theorem predecessor {b : Bool} (h : PlainLayer P C J) (e : SecondaryEdge P C I J b) :
    PlainLayer P C I := by
  obtain ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩ := h
  cases b with
  | false => exact ⟨⟨D, hD, .cons e hp⟩, ⟨D', hD', .cons e hp'⟩⟩
  | true => exact ⟨⟨D', hD', .cons e hp'⟩, ⟨D, hD, .cons e hp⟩⟩

end PlainLayer

namespace FreeLayer

variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem active {s : Bool} (h : FreeLayer P C I s) : ActiveLayer P C I := by
  obtain ⟨D, hD, hp⟩ := h.2
  exact ⟨D, hD, s, hp⟩

theorem sign_unique {s t : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C I t) : s = t := by
  obtain ⟨hn, D, hD, hp⟩ := h
  obtain ⟨_, D', hD', hp'⟩ := k
  cases s <;> cases t
  · rfl
  · exact False.elim (hn ⟨⟨D, hD, hp⟩, ⟨D', hD', hp'⟩⟩)
  · exact False.elim (hn ⟨⟨D', hD', hp'⟩, ⟨D, hD, hp⟩⟩)
  · rfl

theorem edge_sign {s t b : Bool} (h : FreeLayer P C I s) (k : FreeLayer P C J t)
    (e : SecondaryEdge P C I J b) : s = Bool.xor b t := by
  obtain ⟨D, hD, hp⟩ := k.2
  exact h.sign_unique ⟨h.1, D, hD, .cons e hp⟩

theorem direct_sign {s : Bool} (h : FreeLayer P C I s) (hd : DirectLayer P C I) :
    s = false := h.sign_unique ⟨h.1, I, hd, .nil I⟩

end FreeLayer

namespace Expr

variable {S : Type u}

@[simp] theorem normalForm_idem (M : Expr S) : M.normalForm.normalForm = M.normalForm := by
  classical
  by_cases h : WeaklyNormalizing M
  · exact normalForm_of_normal (normalForm_spec h).2
  · simp only [normalForm, dite_eq_right h]

theorem normalForm_rename {M : Expr S} (h : WeaklyNormalizing M) (ρ : Nat → Nat) :
    (M.rename ρ).normalForm = M.normalForm.rename ρ :=
  normalForm_eq ((normalForm_spec h).1.rename ρ) ((normalForm_spec h).2.rename ρ)

end Expr

namespace HasType

variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}

theorem lookup_sorted (hΓ : ValidContext P Γ) {n : Nat} {A : Expr S}
    (hn : Lookup Γ n A) : ∃ s, HasType P Γ A (.sort s) := by
  induction hΓ generalizing n A with
  | nil => cases hn
  | cons hΓ hB ih =>
      cases hn with
      | zero => exact ⟨_, .weaken hB hB⟩
      | succ _ hn =>
          obtain ⟨s, hs⟩ := ih hn
          exact ⟨s, .weaken hs hB⟩

theorem neutral_type_sorted {M A : Expr S} (hn : Neutral M)
    (ht : HasType P Γ M A) : ∃ s, HasType P Γ A (.sort s) := by
  cases hn with
  | var n =>
      obtain ⟨D, hD, hc⟩ := ht.generation
      obtain ⟨s, hs⟩ := lookup_sorted ht.valid hD
      obtain ⟨t, rfl⟩ | hA := ht.regularity
      · obtain ⟨Q, hDQ, hsQ⟩ := (show Converts D (.sort t) from .symm _ _ hc).join
        have heq := (Normal.sort t).reduces_eq hsQ
        subst Q
        exact ⟨s, hs.subject_reduces hDQ⟩
      · exact hA
  | app _ => exact ht.application_type_sorted

end HasType

namespace Profile

variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}

@[simp] theorem normalForm (T : Expr S) : Profile P Γ T.normalForm = Profile P Γ T := by
  simp only [Profile, Expr.normalForm_idem]

theorem of_normal {T : Expr S} (hn : Normal T) :
    Profile P Γ T = {s | HasType P Γ T (.sort s)} := by
  simp only [Profile, Expr.normalForm_of_normal hn]

theorem sort (hΓ : ValidContext P Γ) (s : S) :
    Profile P Γ (.sort s) = AxProfile P s := by
  rw [of_normal (Normal.sort s)]
  ext t
  constructor
  · intro h
    obtain ⟨u, hu, hc⟩ := h.generation
    have he := hc.sort_inj
    subst u
    exact hu
  · exact HasType.sort_of_valid hΓ

theorem neutral {M : Expr S} {s : S} (hn : Normal M) (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : Profile P Γ M = {s} := by
  rw [of_normal hn]
  ext t
  constructor
  · intro h
    exact (ht.neutral_unique hne h).sort_inj.symm
  · intro h
    have he : t = s := h
    subst t
    exact ht

theorem neutral_axiom {M : Expr S} {s : S} (hne : Neutral M)
    (ht : HasType P Γ M (.sort s)) : (AxProfile P s).Nonempty := by
  obtain ⟨t, ht⟩ := ht.neutral_type_sorted hne
  obtain ⟨u, hu, hc⟩ := ht.generation
  exact ⟨u, hu⟩

theorem pi {A B : Expr S} (hnA : Normal A) (hnB : Normal B) :
    Profile P Γ (.pi A B) = OutProfile P (Profile P Γ A) (Profile P (A :: Γ) B) := by
  rw [of_normal (hnA.pi hnB), of_normal hnA, of_normal hnB]
  ext s
  constructor
  · intro ht
    obtain ⟨a, b, c, hA, hB, hr, hc⟩ := ht.generation_pi
    have he := hc.sort_inj
    subst c
    exact ⟨a, hA, b, hB, hr⟩
  · rintro ⟨a, hA, b, hB, hr⟩
    exact .product hA hB hr

theorem converts {A B : Expr S} (hA : WeaklyNormalizing A) (hB : WeaklyNormalizing B)
    (hc : Converts A B) : Profile P Γ A = Profile P Γ B := by
  simp only [Profile, Expr.normalForm_converts hA hB hc]

theorem growth (hw : SystemWeaklyNormalizing P) {T : Expr S}
    (hT : WeaklyNormalizing T) (hΔ : ValidContext P Δ) (σ : Nat → Expr S)
    (hσ : TypedSubstitution P Γ Δ σ) : Profile P Γ T ⊆ Profile P Δ (T.subst σ) := by
  intro s hs
  have ht : HasType P Δ (T.normalForm.subst σ) (.sort s) :=
    hs.subst hΔ σ hσ
  have hr := (Expr.normalForm_spec hT).1.subst σ
  have hrn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).1
  have hn := (Expr.normalForm_spec (ht.weaklyNormalizing hw)).2
  have heq := Expr.normalForm_eq (hr.trans hrn) hn
  change HasType P Δ (T.subst σ).normalForm (.sort s)
  rw [heq]
  exact ht.normalForm hw

theorem feasible {T : Expr S} (hT : WeaklyNormalizing T)
    (hne : (Profile P Γ T).Nonempty) : FeasibleProfile P (Profile P Γ T) := by
  obtain ⟨s, hs⟩ := hne
  exact ⟨⟨s, hs⟩, Γ, T.normalForm, hs.valid, (Expr.normalForm_spec hT).2, normalForm T⟩

end Profile

/-! Finite component order for the exact signed graphs of the manuscript. -/
namespace Reach
variable {V : Type u} (E : V → V → Bool → Prop)

def component (v : V) : Set V := {w | Reach E v w ∧ Reach E w v}

theorem mem_component (v : V) : v ∈ component E v := ⟨.refl v, .refl v⟩

theorem component_isComponent (v : V) : IsComponent E (component E v) :=
  ⟨v, mem_component E v, fun _ => Iff.rfl⟩

theorem component_eq {v w : V} (h : Reach E v w) (k : Reach E w v) :
    component E v = component E w := by
  ext z
  exact ⟨fun hz => ⟨k.trans hz.1, hz.2.trans h⟩,
    fun hz => ⟨h.trans hz.1, hz.2.trans k⟩⟩

variable [Fintype V]
open Classical

noncomputable def predecessors (v : V) : Finset V := Finset.univ.filter fun w => Reach E w v
noncomputable def rank (v : V) : Nat := (predecessors E v).card

@[simp] theorem mem_predecessors {v w : V} : w ∈ predecessors E v ↔ Reach E w v := by
  simp [predecessors]

theorem rank_mono {v w : V} (h : Reach E v w) : rank E v ≤ rank E w := by
  apply Finset.card_le_card
  intro z hz
  exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)

theorem reverse_of_rank_eq {v w : V} (h : Reach E v w) (he : rank E v = rank E w) :
    Reach E w v := by
  have hs : predecessors E v ⊆ predecessors E w := by
    intro z hz
    exact (mem_predecessors E).mpr (((mem_predecessors E).mp hz).trans h)
  have he' := Finset.eq_of_subset_of_card_le hs (le_of_eq he.symm)
  apply (mem_predecessors E).mp
  rw [he']
  exact (mem_predecessors E).mpr (.refl _)

theorem component_eq_of_rank_eq {v w : V} (h : Reach E v w)
    (he : rank E v = rank E w) : component E v = component E w :=
  component_eq E h (reverse_of_rank_eq E h he)

end Reach

namespace PlainLayer
variable {S : Type u} {P : Specification S} {C : Set (Set S)} {I J : Set S}

theorem predecessor_path (h : PlainLayer P C J) (hp : Reach (SecondaryEdge P C) I J) :
    PlainLayer P C I := by
  obtain ⟨b, hp⟩ := hp
  induction hp with
  | nil => exact h
  | cons he _ ih => exact (ih h).predecessor he

theorem component_plain (h : PlainLayer P C I) :
    ∀ J ∈ Reach.component (SecondaryEdge P C) I, PlainLayer P C J := by
  intro J hJ
  exact h.predecessor_path hJ.2
end PlainLayer

namespace IsComponent
variable {V : Type u} {E : V → V → Bool → Prop} {C : Set V}
open Classical

noncomputable def signing (hc : IsComponent E C) (v : V) : Bool :=
  if h : v ∈ C then (hc.connected hc.choose_spec.1 h).choose else false

theorem signing_path (hc : IsComponent E C) {v : V} (hv : v ∈ C) :
    SignedPath E hc.choose v (hc.signing v) := by
  unfold signing
  rw [dite_eq_left hv]
  exact (hc.connected hc.choose_spec.1 hv).choose_spec

theorem signing_cross (hc : IsComponent E C)
    (hn : ∀ v ∈ C, ¬ SignedPath E v v true)
    {v w : V} {p : Bool} (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w p) :
    hc.signing w = Bool.xor (hc.signing v) p := by
  exact (hc.signing_path hw).parity_unique ((hc.signing_path hv).append hp)
    (hc.connected hw hc.choose_spec.1) (hn _ hc.choose_spec.1)
end IsComponent
end PureTypeSystem

end OAI
