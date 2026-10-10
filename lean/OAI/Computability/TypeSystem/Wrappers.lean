import OAI.Computability.TypeSystem.Labelled
import OAI.Computability.TypeSystem.Profiles

namespace OAI

/- Concrete labelled term operations for wrappers. -/
namespace PureTypeSystem.Labelled
universe u

namespace Expr
variable {S : Type u}
def data (M : PureTypeSystem.Expr S) : Expr S :=
  match M with
  | .var n => .var n
  | .sort s => .sort s
  | .app f a => .app .dd (data f) (data a)
  | .lam A b => .lam .dd (data A) (data b)
  | .pi A B => .pi .dd (data A) (data B)

@[simp] theorem erase_data (M : PureTypeSystem.Expr S) : (Expr.data M).erase = M := by
  induction M <;> simp_all [data, erase]

@[simp] theorem data_rename (M : PureTypeSystem.Expr S) (ρ : Nat → Nat) :
    (Expr.data (M.rename ρ)) = (Expr.data M).rename ρ := by
  induction M generalizing ρ <;> simp_all [data, rename, PureTypeSystem.Expr.rename]

@[simp] theorem data_subst (M : PureTypeSystem.Expr S) (σ : Nat → PureTypeSystem.Expr S) :
    (Expr.data (M.subst σ)) = (Expr.data M).subst (data ∘ σ) := by
  have hl (σ : Nat → PureTypeSystem.Expr S) :
      data ∘ PureTypeSystem.Expr.liftSub σ = liftSub (data ∘ σ) := by
    funext n; cases n <;> simp [PureTypeSystem.Expr.liftSub, liftSub, data]
  induction M generalizing σ <;>
    simp_all only [data, subst, PureTypeSystem.Expr.subst, Function.comp_apply]

@[simp] theorem data_instantiate (b a : PureTypeSystem.Expr S) :
    (Expr.data (b.instantiate a)) = (Expr.data b).instantiate (Expr.data a) := by
  have h : data ∘ PureTypeSystem.Expr.single a = single (Expr.data a) := by
    funext n; cases n <;> rfl
  simp only [PureTypeSystem.Expr.instantiate, data_subst, h, instantiate]

theorem data_allData (M : PureTypeSystem.Expr S) : (Expr.data M).AllData := by
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app f a hf ha => exact .app hf ha
  | lam A b hA hb => exact .lam hA hb
  | pi A B hA hB => exact .pi hA hB

theorem data_wellModed (M : PureTypeSystem.Expr S) :
    WellModed (fun _ => .data) (Expr.data M) .data := by
  have h : modeCons .data (fun _ => Mode.data) = fun _ => Mode.data := by
    funext n; cases n <;> rfl
  induction M with
  | var n => exact .var n
  | sort s => exact .sort s
  | app f a hf ha => exact .app hf ha
  | lam A b hA hb =>
      apply WellModed.lam hA
      simpa only [Label.domain, Label.result, h] using hb
  | pi A B hA hB =>
      apply WellModed.pi hA
      simpa only [Label.domain, h] using hB

/-- Nondependent labelled arrow; its codomain is shifted, not captured. -/
def arrow (l : Label) (A B : Expr S) : Expr S := .pi l A (B.rename Nat.succ)
def constLam (l : Label) (A b : Expr S) : Expr S := .lam l A (b.rename Nat.succ)

@[simp] theorem arrow_rename (l : Label) (A B : Expr S) (ρ : Nat → Nat) :
    (arrow l A B).rename ρ = arrow l (A.rename ρ) (B.rename ρ) := by
  simp only [arrow, rename, rename_comp]
  rfl

@[simp] theorem arrow_subst (l : Label) (A B : Expr S) (σ : Nat → Expr S) :
    (arrow l A B).subst σ = arrow l (A.subst σ) (B.subst σ) := by
  simp only [arrow, subst, subst_rename, rename_subst]
  rfl

@[simp] theorem constLam_rename (l : Label) (A b : Expr S) (ρ : Nat → Nat) :
    (constLam l A b).rename ρ = constLam l (A.rename ρ) (b.rename ρ) := by
  simp only [constLam, rename, rename_comp]
  rfl

@[simp] theorem constLam_subst (l : Label) (A b : Expr S) (σ : Nat → Expr S) :
    (constLam l A b).subst σ = constLam l (A.subst σ) (b.subst σ) := by
  simp only [constLam, subst, subst_rename, rename_subst]
  rfl

@[simp] theorem instantiate_raise (M a : Expr S) : (M.rename Nat.succ).instantiate a = M :=
  subst_lift_single M a
end Expr

namespace Beta
variable {S : Type u} {M N : PureTypeSystem.Expr S}
theorem data (h : PureTypeSystem.Beta M N) : Beta (Expr.data M) (Expr.data N) := by
  induction h with
  | head A b a =>
      simpa only [Expr.data, Expr.data_instantiate] using
        (Beta.head .dd (Expr.data A) (Expr.data b) (Expr.data a))
  | app_left h ih => exact .app_left ih
  | app_right h ih => exact .app_right ih
  | lam_domain h ih => exact .lam_domain ih
  | lam_body h ih => exact .lam_body ih
  | pi_domain h ih => exact .pi_domain ih
  | pi_body h ih => exact .pi_body ih
end Beta
namespace Converts
variable {S : Type u} {M N : PureTypeSystem.Expr S}
theorem data (h : PureTypeSystem.Converts M N) : Converts (Expr.data M) (Expr.data N) := by
  induction h with
  | rel a b h => exact .rel _ _ (Beta.data h)
  | refl a => exact .refl _
  | symm a b h ih => exact .symm _ _ ih
  | trans a b c h h' ih ih' => exact .trans _ _ _ ih ih'
end Converts

namespace HasType
variable {S : Type u} {P : Specification S}
theorem data {Γ : List (PureTypeSystem.Expr S)} {M A : PureTypeSystem.Expr S}
    (h : PureTypeSystem.HasType P Γ M A) : HasType P (Γ.map Expr.data) (Expr.data M) (Expr.data A) := by
  induction h with
  | ax h => exact .ax h
  | var h ih => simpa only [List.map_cons, Expr.data, Expr.data_rename] using HasType.var ih
  | weaken h hA ih ihA =>
      simpa only [List.map_cons, Expr.data_rename] using HasType.weaken ih ihA
  | product hA hB hr ihA ihB => exact .product ihA ihB hr
  | abstraction hb hp ihb ihp => exact .abstraction ihb ihp
  | application hf ha ihf iha =>
      simpa only [Expr.data, Expr.data_instantiate] using HasType.application ihf iha
  | conversion h hA hc ih ihA => exact .conversion ih ihA (Converts.data hc)

variable {Γ : List (Expr S)} {A B M N : Expr S} {s t r : S} {l : Label}
theorem arrow (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t))
    (hr : P.rule s t r) : HasType P Γ (Expr.arrow l A B) (.sort r) :=
  .product hA (.weaken hB hA) hr

theorem constLam (hM : HasType P Γ M B) (hA : HasType P Γ A (.sort s))
    (hPi : HasType P Γ (Expr.arrow l A B) (.sort r)) :
    HasType P Γ (Expr.constLam l A M) (Expr.arrow l A B) :=
  .abstraction (.weaken hM hA) hPi

theorem apply_arrow (hM : HasType P Γ M (Expr.arrow l A B)) (hN : HasType P Γ N A) :
    HasType P Γ (.app l M N) B := by
  simpa only [Expr.instantiate_raise] using HasType.application hM hN
end HasType

namespace WellModed
variable {S : Type u} {γ : Nat → Mode} {A B M : Expr S} {l : Label}
/-- Data syntax cannot inspect a proof-mode image, even inside annotations. -/
theorem data_subst_congr {M : Expr S} {m : Mode} (h : WellModed γ M m)
    (hm : m = .data) (σ τ : Nat → Expr S)
    (he : ∀ n, γ n = .data → σ n = τ n) : M.subst σ = M.subst τ := by
  have hlift {γ : Nat → Mode} {σ τ : Nat → Expr S}
      (he : ∀ n, γ n = .data → σ n = τ n) (d : Mode) :
      ∀ n, modeCons d γ n = .data → Expr.liftSub σ n = Expr.liftSub τ n := by
    intro n hn
    cases n with
    | zero => rfl
    | succ n => exact congrArg (Expr.rename Nat.succ) (he n hn)
  induction h generalizing σ τ with
  | var n => exact he n hm
  | sort s => rfl
  | @app γ l f a hf ha ihf iha =>
      cases l with
      | dd => exact congrArg₂ (Expr.app .dd) (ihf rfl σ τ he) (iha rfl σ τ he)
      | dp => cases hm
      | pp => cases hm
  | @lam γ l A b hA hb ihA ihb =>
      cases l with
      | dd =>
          exact congrArg₂ (Expr.lam .dd) (ihA rfl σ τ he)
            (ihb rfl _ _ (hlift he .data))
      | dp => cases hm
      | pp => cases hm
  | @pi γ l A B hA hB ihA ihB =>
      exact congrArg₂ (Expr.pi l) (ihA rfl σ τ he) (ihB rfl _ _ (hlift he _))

theorem proof_instantiate_irrelevant {b a a' : Expr S}
    (hb : WellModed (modeCons .proof γ) b .data) :
    b.instantiate a = b.instantiate a' := by
  apply hb.data_subst_congr rfl
  intro n hn
  cases n with
  | zero => cases hn
  | succ n => rfl

theorem raise {m : Mode} (h : WellModed γ M m) (d : Mode) :
    WellModed (modeCons d γ) (M.rename Nat.succ) m :=
  h.rename _ (fun _ => rfl)

theorem arrow (hA : WellModed γ A .data) (hB : WellModed γ B .data) :
    WellModed γ (Expr.arrow l A B) .data := .pi hA (hB.raise _)

theorem constLam (hA : WellModed γ A .data) (hM : WellModed γ M l.result) :
    WellModed γ (Expr.constLam l A M) l.result := .lam hA (hM.raise _)
end WellModed

/-- Sorting at a profile records all source sorting judgments, not an exact
profile assertion; wrappers intentionally permit profile growth. -/
def SortedAt {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (A : Expr S) (I : Set S) : Prop := ∀ s ∈ I, HasType P Γ A (.sort s)
namespace SortedAt
variable {S : Type u} {P : Specification S} {Γ : List (Expr S)}
    {A B : Expr S} {I J K : Set S}
theorem mono (h : SortedAt P Γ A I) (hJI : J ⊆ I) : SortedAt P Γ A J :=
  fun _ hs => h _ (hJI hs)

theorem arrow (hA : SortedAt P Γ A I) (hB : SortedAt P Γ B J) (l : Label)
    (hK : K ⊆ OutProfile P I J) : SortedAt P Γ (Expr.arrow l A B) K := by
  intro r hr
  obtain ⟨s, hs, t, ht, hst⟩ := hK hr
  exact (hA s hs).arrow (hB t ht) hst

theorem raise (h : SortedAt P Γ A I) {D : Expr S} {s : S}
    (hD : HasType P Γ D (.sort s)) : SortedAt P (D :: Γ) (A.rename Nat.succ) I :=
  fun _ hs => .weaken (h _ hs) hD
end SortedAt

/-- The exact positive product-edge lift/projection beta cancellation. -/
theorem positive_cancel {S : Type u} (l : Label) (D e t : Expr S) :
    Beta (.app l (Expr.constLam l D t) e) t := by
  simpa only [Expr.constLam, Expr.instantiate_raise] using Beta.head l D (t.rename Nat.succ) e

end PureTypeSystem.Labelled

/-! Finite simultaneous normal data witnesses.
Feasibility is semantic, so these lemmas do not assume a profile-generation
conjecture. The extra inhabitants are genuine fresh context variables. -/
namespace PureTypeSystem

section
universe u

namespace Lookup
variable {S : Type u} {Γ Δ : List (Expr S)} {n : Nat} {A : Expr S}
theorem append_right (h : Lookup Γ n A) (Δ : List (Expr S)) : Lookup (Γ ++ Δ) n A := by
  induction h with
  | zero => exact .zero _ _
  | succ C h ih => exact .succ C ih

theorem append_left (h : Lookup Δ n A) (Γ : List (Expr S)) :
    Lookup (Γ ++ Δ) (n + Γ.length) (A.rename (fun i => i + Γ.length)) := by
  induction Γ with
  | nil => simpa only [List.length_nil, List.nil_append, Nat.add_zero, ← Function.id_def, Expr.rename_id] using h
  | cons B Γ ih =>
      have hh := Lookup.succ B ih
      simpa only [List.length_cons, List.cons_append, Expr.rename_comp, Function.comp_def,
        Nat.add_assoc, Nat.succ_eq_add_one] using hh
end Lookup

namespace ValidContext
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)}
theorem append (hΓ : ValidContext P Γ) (hΔ : ValidContext P Δ) : ValidContext P (Γ ++ Δ) := by
  induction hΓ with
  | nil => exact hΔ
  | cons hΓ hA ih =>
      apply ValidContext.cons ih
      have hh := hA.rename ih id (fun n A hn => by
        simpa only [Expr.rename_id, id_eq] using HasType.lookup ih (hn.append_right Δ))
      simpa only [Expr.rename_id] using hh
end ValidContext

namespace HasType
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {M A : Expr S}
theorem append_right (h : HasType P Γ M A) (hΔ : ValidContext P Δ) :
    HasType P (Γ ++ Δ) M A := by
  have hv := h.valid.append hΔ
  simpa only [Expr.rename_id] using h.rename hv id (fun n B hn => by
    simpa only [Expr.rename_id, id_eq] using HasType.lookup hv (hn.append_right Δ))

theorem append_left (h : HasType P Δ M A) (hΓ : ValidContext P Γ) :
    HasType P (Γ ++ Δ) (M.rename (fun i => i + Γ.length)) (A.rename (fun i => i + Γ.length)) :=
  h.rename (hΓ.append h.valid) _ (fun _ _ hn => HasType.lookup (hΓ.append h.valid) (hn.append_left Γ))
end HasType

/-- An actual normal witness of a feasible profile, with a declared inhabitant.
All the sorting judgments, rather than one selected sort, are retained. -/
def HasWitness {S : Type u} (P : Specification S) (Γ : List (Expr S)) (I : Set S) : Prop :=
  ∃ T e : Expr S, Normal T ∧ (∀ s ∈ I, HasType P Γ T (.sort s)) ∧ HasType P Γ e T

namespace HasWitness
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {I : Set S}
theorem append_left (h : HasWitness P Δ I) (hΓ : ValidContext P Γ) : HasWitness P (Γ ++ Δ) I := by
  obtain ⟨T, e, hT, hs, he⟩ := h
  exact ⟨_, _, hT.rename _, fun s hi => (hs s hi).append_left hΓ, he.append_left hΓ⟩

theorem append_right (h : HasWitness P Γ I) (hΔ : ValidContext P Δ) : HasWitness P (Γ ++ Δ) I := by
  obtain ⟨T, e, hT, hs, he⟩ := h
  exact ⟨T, e, hT, fun s hi => (hs s hi).append_right hΔ, he.append_right hΔ⟩
end HasWitness

namespace FeasibleProfile
variable {S : Type u} {P : Specification S} {I : Set S}
theorem witness (h : FeasibleProfile P I) : ∃ Γ, ValidContext P Γ ∧ HasWitness P Γ I := by
  obtain ⟨⟨s, hs⟩, Γ, T, hΓ, hn, hp⟩ := h
  have ht : ∀ a ∈ I, HasType P Γ T (.sort a) := by
    intro a ha
    rw [← hp] at ha
    simpa only [Profile, Set.mem_ofPred_eq, Expr.normalForm_of_normal hn] using ha
  exact ⟨T :: Γ, .cons hΓ (ht s hs), _, _, hn.rename _,
    fun a ha => .weaken (ht a ha) (ht s hs), .var (ht s hs)⟩

theorem finite_witnesses (F : Finset (Set S)) (hF : ∀ I ∈ F, FeasibleProfile P I) :
    ∃ Γ, ValidContext P Γ ∧ ∀ I ∈ F, HasWitness P Γ I := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨[], .nil, by simp⟩
  | @insert I F hi ih =>
      obtain ⟨Γ, hv, hw⟩ := ih (fun J hJ => hF J (Finset.mem_insert_of_mem hJ))
      obtain ⟨Δ, hd, hI⟩ := (hF I (Finset.mem_insert_self _ _)).witness
      refine ⟨Δ ++ Γ, hd.append hv, ?_⟩
      intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact hI.append_right hv
      · exact (hw J hJ).append_left hd
end FeasibleProfile

namespace Labelled
/-- The data context has no proof-mode declarations. Its finite witness terms
are literal all-data embeddings and their erased types are normal. -/
structure DataWitnessContext {S : Type u} (P : Specification S) (F : Finset (Set S)) where
  context : List (Expr S)
  valid : ValidContext P context
  allData : ∀ A ∈ context, A.AllData
  witness : ∀ I ∈ F, ∃ T e : Expr S, T.AllData ∧ e.AllData ∧
    PureTypeSystem.Normal T.erase ∧ SortedAt P context T I ∧ HasType P context e T

namespace ValidContext
variable {S : Type u} {P : Specification S} {Γ : List (PureTypeSystem.Expr S)}
theorem data (h : PureTypeSystem.ValidContext P Γ) : ValidContext P (Γ.map Expr.data) := by
  induction h with
  | nil => exact .nil
  | cons hΓ hA ih => exact .cons ih (HasType.data hA)
end ValidContext

noncomputable def DataWitnessContext.ofFeasible {S : Type u} {P : Specification S}
    (F : Finset (Set S)) (hF : ∀ I ∈ F, FeasibleProfile P I) : DataWitnessContext P F := by
  let hh := FeasibleProfile.finite_witnesses F hF
  let Γ := hh.choose
  have hv : PureTypeSystem.ValidContext P Γ := hh.choose_spec.1
  refine ⟨Γ.map Expr.data, ValidContext.data hv, ?_, ?_⟩
  · intro A hA
    obtain ⟨B, _, rfl⟩ := List.mem_map.mp hA
    exact Expr.data_allData B
  · intro I hi
    obtain ⟨T, e, hT, hs, he⟩ := hh.choose_spec.2 I hi
    exact ⟨Expr.data T, Expr.data e, Expr.data_allData T, Expr.data_allData e,
      by simpa only [Expr.erase_data] using hT, fun s hs' => HasType.data (hs s hs'), HasType.data he⟩

end Labelled
end

/- Finite signed-path choices for channels. -/

namespace SignedPath
variable {V : Type*} {E : V → V → Bool → Prop}

/-- Any odd walk has a negative edge with an even remaining suffix. -/
theorem negative_even_suffix {v w : V} (h : SignedPath E v w true) :
    ∃ p g, Reach E v p ∧ E p g true ∧ SignedPath E g w false := by
  generalize hq : true = q at h
  induction h with
  | nil v => cases hq
  | @cons u v w p q he ht ih =>
      cases p <;> cases q
      · cases hq
      · obtain ⟨p, g, hp, he', hg⟩ := ih rfl
        exact ⟨p, g, (Reach.single he).trans hp, he', hg⟩
      · exact ⟨u, v, Reach.refl u, he, ht⟩
      · cases hq

/-- Restrict a finite walk when all of its intermediate points lie in a set. -/
theorem restrict {C : Set V} {v w : V} {p : Bool}
    (h : SignedPath E v w p) (hv : v ∈ C)
    (hi : ∀ z, Reach E v z → Reach E z w → z ∈ C) :
    SignedPath (fun x y p => E x y p ∧ x ∈ C ∧ y ∈ C) v w p := by
  induction h with
  | nil v => exact .nil _
  | @cons u v w p q he ht ih =>
      have hv' := hi v (Reach.single he) ⟨q, ht⟩
      exact .cons ⟨he, hv, hv'⟩ (ih hv' (fun z hz hzw =>
        hi z ((Reach.single he).trans hz) hzw))
end SignedPath

namespace IsComponent
variable {V : Type*} {E : V → V → Bool → Prop} {C : Set V}

/-- An odd closed walk in an SCC supplies both parities between all vertices. -/
theorem all_parities (hC : IsComponent E C) {r v w : V}
    (hr : r ∈ C) (ho : SignedPath E r r true) (hv : v ∈ C) (hw : w ∈ C)
    (b : Bool) : SignedPath E v w b := by
  obtain ⟨p, hp⟩ := hC.connected hv hr
  obtain ⟨q, hq⟩ := hC.connected hr hw
  have h₀ := hp.append hq
  have h₁ := (hp.append ho).append hq
  cases p <;> cases q <;> cases b <;> first | exact h₀ | exact h₁

theorem restrict_path (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b) :
    SignedPath (fun x y p => E x y p ∧ x ∈ C ∧ y ∈ C) v w b :=
  hp.restrict hv (fun _ hz hzw => hC.between hv hw hz hzw)

/-- No odd cycle makes the return parity uniquely determined by the outward one. -/
theorem return_parity (hC : IsComponent E C) {v w : V} {b : Bool}
    (hv : v ∈ C) (hw : w ∈ C) (hp : SignedPath E v w b)
    (ho : ¬ SignedPath E v v true) : SignedPath E w v b := by
  obtain ⟨q, hq⟩ := hC.connected hw hv
  have hc := hp.append hq
  cases b <;> cases q <;> first | exact hq | exact False.elim (ho hc)

/-- The three internal path roles needed by the first data channel, without
assuming that the secondary component itself has an odd cycle. -/
theorem negative_routes (hC : IsComponent E C) {J k : V}
    (hJ : J ∈ C) (hk : k ∈ C) (hJk : E J k false)
    (hn : ∃ a ∈ C, ∃ b ∈ C, E a b true) :
    ∃ p ∈ C, ∃ g ∈ C, E p g true ∧ SignedPath E k p true ∧
      SignedPath E p k true ∧ SignedPath E g J false := by
  classical
  by_cases ho : ∃ r ∈ C, SignedPath E r r true
  · obtain ⟨r, hr, ho⟩ := ho
    obtain ⟨p, hp, g, hg, he⟩ := hn
    exact ⟨p, hp, g, hg, he, hC.all_parities hr ho hk hp true,
      hC.all_parities hr ho hp hk true, hC.all_parities hr ho hg hJ false⟩
  · have no_odd (r : V) (hr : r ∈ C) : ¬ SignedPath E r r true :=
      fun hh => ho ⟨r, hr, hh⟩
    obtain ⟨a, ha, b, hb, he⟩ := hn
    obtain ⟨q, hbk⟩ := hC.connected hb hk
    have hedge : ∃ p ∈ C, ∃ g ∈ C, E p g true ∧ SignedPath E g k false := by
      cases q with
      | false => exact ⟨a, ha, b, hb, he, hbk⟩
      | true =>
          obtain ⟨p, g, hbp, hpg, hgk⟩ := hbk.negative_even_suffix
          have hp := hC.between hb hk hbp ((Reach.single hpg).trans ⟨false, hgk⟩)
          have hg := hC.between hb hk (hbp.trans (Reach.single hpg)) ⟨false, hgk⟩
          exact ⟨p, hp, g, hg, hpg, hgk⟩
    obtain ⟨p, hp, g, hg, hpg, hgk⟩ := hedge
    have hpk : SignedPath E p k true := .cons hpg hgk
    have hkp := hC.return_parity hp hk hpk (no_odd p hp)
    have hkJ := hC.return_parity hJ hk (.singleton hJk) (no_odd J hJ)
    exact ⟨p, hp, g, hg, hpg, hkp, hpk, hgk.append hkJ⟩
end IsComponent

namespace ForbiddenConfiguration
universe u
variable {S : Type u} {P : Specification S} {C : Set (Set S)}

/-- Source choice-of-paths conclusion, retaining the actual triples and all
profile and seed hypotheses of the forbidden configuration. -/
theorem channel_paths (h : ForbiddenConfiguration P C) :
    ∃ D : Set (Set S), IsComponent (SecondaryEdge P C) D ∧
    ∃ I J k s p n g j h',
      ProfileTriple P I J k ∧ J ∈ D ∧ k ∈ D ∧ ({s} : Set S) ∈ D ∧
      (AxProfile P s).Nonempty ∧ PositivePath (PrimaryEdge P) (AxProfile P s) I ∧
      ProfileTriple P p n g ∧ p ∈ D ∧ g ∈ D ∧ n ∈ ObservationLayers P C ∧
      SignedPath (SecondaryEdge P C) k p true ∧
      SignedPath (SecondaryEdge P C) p k true ∧
      SignedPath (SecondaryEdge P C) g J false ∧
      DirectLayer P C j ∧ SignedPath (SecondaryEdge P C) k j true ∧
      DirectLayer P C h' ∧ SignedPath (SecondaryEdge P C) k h' false ∧
      SignedPath (SecondaryEdge P C) p h' true := by
  obtain ⟨D, hD, hplain, hneg, I, J, k, s, hI, hJ, hk, hs, hax, hpath⟩ := h
  have path_layer {T A : Set S} {b : Bool}
      (hp : SignedPath (SecondaryEdge P C) T A b) (hA : A ∈ ObservationLayers P C) :
      T ∈ ObservationLayers P C := by
    cases hp with
    | nil => exact hA
    | cons he ht => cases he with
      | positive hsrc _ _ => exact hsrc
      | negative hsrc _ _ _ => exact hsrc
  have layer_of_plain {T : Set S} (ht : PlainLayer P C T) : T ∈ ObservationLayers P C := by
    obtain ⟨A, hA, hp⟩ := ht.1
    exact path_layer hp hA.1
  have hJ' := layer_of_plain (hplain J hJ)
  have hk' := layer_of_plain (hplain k hk)
  have hJk : SecondaryEdge P C J k false := .positive hJ' hk' (.codomain hI)
  obtain ⟨p, hp, g, hg, he, hkp, hpk, hgJ⟩ := hD.negative_routes hJ hk hJk hneg
  cases he with
  | negative _ hn _ htr =>
      obtain ⟨⟨h', hh', hkh'⟩, ⟨j, hj, hkj⟩⟩ := hplain k hk
      exact ⟨D, hD, I, J, k, s, p, _, g, j, h', hI, hJ, hk, hs, hax, hpath,
        htr, hp, hg, hn, hkp, hpk, hgJ, hj, hkj, hh', hkh', hpk.append hkh'⟩
end ForbiddenConfiguration

end PureTypeSystem

namespace PureTypeSystem.Labelled

section
universe u
open Classical

/-- A legal mode-preserving change of names. No hypotheses about convertibility
or proof existence are packed into the map. -/
structure Embedding {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (γ : Nat → Mode) (Δ : List (Expr S)) (δ : Nat → Mode) where
  names : Nat → Nat
  valid : ValidContext P Δ
  typed : ∀ n A, Lookup Γ n A → HasType P Δ (.var (names n)) (A.rename names)
  modes : ∀ n, δ (names n) = γ n

namespace Embedding
variable {S : Type u} {P : Specification S}
    {Γ Δ Θ : List (Expr S)} {γ δ θ : Nat → Mode}

def refl (hv : ValidContext P Γ) (γ : Nat → Mode) : Embedding P Γ γ Γ γ where
  names := id
  valid := hv
  typed n A hn := by simpa only [Expr.rename_id,id_eq] using HasType.lookup hv hn
  modes _ := rfl

theorem typing (e : Embedding P Γ γ Δ δ) {M A : Expr S} (h : HasType P Γ M A) :
    HasType P Δ (M.rename e.names) (A.rename e.names) := h.rename e.valid e.names e.typed

theorem moded (e : Embedding P Γ γ Δ δ) {M : Expr S} {m : Mode}
    (h : WellModed γ M m) : WellModed δ (M.rename e.names) m := h.rename _ e.modes

def comp (e : Embedding P Γ γ Δ δ) (f : Embedding P Δ δ Θ θ) : Embedding P Γ γ Θ θ where
  names := f.names ∘ e.names
  valid := f.valid
  typed n A hn := by simpa only [Expr.rename_comp,Expr.rename,Function.comp_apply] using f.typing (e.typed n A hn)
  modes n := (f.modes _).trans (e.modes n)

def cons {A : Expr S} {s : S} (hA : HasType P Γ A (.sort s)) (d : Mode) :
    Embedding P Γ γ (A :: Γ) (modeCons d γ) where
  names := Nat.succ
  valid := .cons hA.valid hA
  typed _n _B hn := .weaken (HasType.lookup hA.valid hn) hA
  modes _ := rfl

def lift (e : Embedding P Γ γ Δ δ) {A : Expr S} {s : S}
    (hA : HasType P Γ A (.sort s)) (d : Mode) :
    Embedding P (A :: Γ) (modeCons d γ) (A.rename e.names :: Δ) (modeCons d δ) where
  names := Expr.liftRen e.names
  valid := .cons e.valid (e.typing hA)
  typed n B hn := by
    cases hn with
    | zero =>
      simpa only [Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.rename] using HasType.var (e.typing hA)
    | succ D hn =>
      simpa only [Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def,Expr.rename] using HasType.weaken (e.typed _ _ hn) (e.typing hA)
  modes n := by cases n with | zero => rfl | succ n => exact e.modes n
end Embedding

namespace ProofContext
variable {S : Type u} {Γ : List (Expr S)} {γ : Nat → Mode}
theorem proof_cons (h : ProofContext Γ γ) {T F : Expr S} (hT : T.Target) :
    ProofContext (Expr.arrow .pp T F :: Γ) (modeCons .proof γ) := by
  intro n A hn hm
  cases hn with
  | zero => exact ⟨_,_,rfl,hT.rename _⟩
  | succ C hn =>
    obtain ⟨R,F,rfl,hR⟩ := h _ _ hn hm
    exact ⟨_,_,rfl,hR.rename _⟩
end ProofContext

namespace Expr
variable {S : Type u}
theorem AllData.wellModed {M : Expr S} (h : M.AllData) :
    WellModed (fun _ => .data) M .data := by
  have he : modeCons .data (fun _ => Mode.data) = fun _ => Mode.data := by
    funext n; cases n <;> rfl
  induction h with
  | var n => exact .var n
  | sort s => exact .sort s
  | app hf ha ihf iha => exact .app ihf iha
  | lam hA hb ihA ihb => apply WellModed.lam ihA; simpa only [Label.domain,Label.result,he] using ihb
  | pi hA hB ihA ihB => apply WellModed.pi ihA; simpa only [Label.domain,he] using ihB

theorem Target.arrow {D T : Expr S} (hT : T.Target)
    (hD : PureTypeSystem.Normal D.erase) : (Expr.arrow .dp D T).Target := by
  refine ⟨.step _ (hT.1.rename _),?_⟩
  exact hD.pi (by simpa only [erase_rename] using hT.2.rename Nat.succ)
end Expr

/-- All finite feasible witnesses with their one fixed choice of terminal type.
The types remain fixed (up to renaming) during proof-context extensions. -/
structure WitnessFamily {S : Type u} (P : Specification S) (Γ : List (Expr S))
    (γ : Nat → Mode) where
  type : Set S → Expr S
  value : Set S → Expr S
  allData : ∀ I, FeasibleProfile P I → (type I).AllData
  normal : ∀ I, FeasibleProfile P I → PureTypeSystem.Normal (type I).erase
  sorted : ∀ I, FeasibleProfile P I → SortedAt P Γ (type I) I
  typed : ∀ I, FeasibleProfile P I → HasType P Γ (value I) (type I)
  type_mode : ∀ I, FeasibleProfile P I → WellModed γ (type I) .data
  value_mode : ∀ I, FeasibleProfile P I → WellModed γ (value I) .data

namespace WitnessFamily
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}

def rename (W : WitnessFamily P Γ γ) (e : Embedding P Γ γ Δ δ) : WitnessFamily P Δ δ where
  type I := (W.type I).rename e.names
  value I := (W.value I).rename e.names
  allData I hI := (W.allData I hI).rename _
  normal I hI := by simpa only [Expr.erase_rename] using (W.normal I hI).rename e.names
  sorted I hI s hs := e.typing (W.sorted I hI s hs)
  typed I hI := e.typing (W.typed I hI)
  type_mode I hI := e.moded (W.type_mode I hI)
  value_mode I hI := e.moded (W.value_mode I hI)

theorem exists_family [Fintype S] : ∃ Γ, ValidContext P Γ ∧
    Nonempty (WitnessFamily P Γ (fun _ => .data)) := by
  let F : Finset (Set S) := Finset.univ.filter (FeasibleProfile P)
  let W := DataWitnessContext.ofFeasible F (by simp only [F,Finset.mem_filter]; tauto)
  have hw (I : Set S) (hI : FeasibleProfile P I) : ∃ T e : Expr S, T.AllData ∧ e.AllData ∧
      PureTypeSystem.Normal T.erase ∧ SortedAt P W.context T I ∧ HasType P W.context e T :=
    W.witness I (by simp [F,hI])
  let ty (I : Set S) : Expr S := if hi : FeasibleProfile P I then (hw I hi).choose else .var 0
  let val (I : Set S) : Expr S := if hi : FeasibleProfile P I then
    (hw I hi).choose_spec.choose else .var 0
  have hp (I : Set S) (hI : FeasibleProfile P I) :
      (ty I).AllData ∧ (val I).AllData ∧ PureTypeSystem.Normal (ty I).erase ∧
      SortedAt P W.context (ty I) I ∧ HasType P W.context (val I) (ty I) := by
    simpa only [ty,val,dite_eq_left hI] using (hw I hI).choose_spec.choose_spec
  exact ⟨W.context,W.valid,⟨⟨ty,val,fun I hi => (hp I hi).1,
    fun I hi => (hp I hi).2.2.1,fun I hi => (hp I hi).2.2.2.1,
    fun I hi => (hp I hi).2.2.2.2,fun I hi => (hp I hi).1.wellModed,
    fun I hi => (hp I hi).2.1.wellModed⟩⟩⟩
end WitnessFamily

/-- A term transformer under one temporary proof input. No product rule is
postulated for its input/output pair; that rule generally does not exist. -/
def Transfer {S : Type u} (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode)
    (A B : Expr S) : Prop :=
  ∃ t, HasType P (A :: Γ) t (B.rename Nat.succ) ∧ WellModed (modeCons .proof γ) t .proof

namespace Transfer
variable {S : Type u} {P : Specification S} {Γ Δ : List (Expr S)} {γ δ : Nat → Mode}
    {A B C D : Expr S} {s t r : S}
theorem refl (hA : HasType P Γ A (.sort s)) : Transfer P Γ γ A A :=
  ⟨_,.var hA,.var 0⟩

theorem rename (h : Transfer P Γ γ A B) (e : Embedding P Γ γ Δ δ)
    (hA : HasType P Γ A (.sort s)) : Transfer P Δ δ (A.rename e.names) (B.rename e.names) := by
  obtain ⟨M,ht,hm⟩ := h
  refine ⟨M.rename (Expr.liftRen e.names),?_,(e.lift hA .proof).moded hm⟩
  simpa only [Embedding.lift,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,Function.comp_def] using (e.lift hA .proof).typing ht

theorem trans (h : Transfer P Γ γ A B) (h' : Transfer P Γ γ B C)
    (hA : HasType P Γ A (.sort s)) (hB : HasType P Γ B (.sort t)) : Transfer P Γ γ A C := by
  obtain ⟨x,hx,mx⟩ := h
  obtain ⟨y,hy,my⟩ := h'.rename (Embedding.cons hA .proof) hB
  refine ⟨y.instantiate x,?_,my.instantiate mx⟩
  simpa only [Expr.instantiate_raise,Embedding.cons] using hy.instantiate hx

theorem positive (hA : HasType P Γ A (.sort s)) (hD : HasType P Γ D (.sort t))
    (hr : P.rule t s r) (hDm : WellModed γ D .data) :
    Transfer P Γ γ A (Expr.arrow .dp D A) := by
  refine ⟨Expr.constLam .dp (D.rename Nat.succ) (.var 0),?_,?_⟩
  · have hpi : HasType P (A :: Γ) (Expr.arrow .dp (D.rename Nat.succ) (A.rename Nat.succ)) (.sort r) := by
      simpa only [Expr.arrow_rename,Expr.rename] using HasType.weaken (hD.arrow (l := .dp) hA hr) hA
    simpa only [Expr.arrow_rename] using
      HasType.constLam (.var hA) (.weaken hD hA) hpi
  · exact (hDm.raise .proof).constLam (.var 0)

/-- The declared converter is inserted before, not after, the temporary input. -/
theorem converter (hC : HasType P Γ (Expr.arrow .pp A B) (.sort r))
    (hA : HasType P Γ A (.sort s)) :
    Transfer P (Expr.arrow .pp A B :: Γ) (modeCons .proof γ)
      (A.rename Nat.succ) (B.rename Nat.succ) := by
  let hA' := HasType.weaken hA hC
  have hc := HasType.weaken (HasType.var hC) hA'
  have hx := HasType.var hA'
  refine ⟨.app .pp (.var 1) (.var 0),?_,.app (.var 1) (.var 0)⟩
  simp only [Expr.arrow_rename,Expr.rename] at hc
  exact HasType.apply_arrow hc hx
end Transfer

end

section
universe u
variable {S : Type u} {P : Specification S}

/-- An actual labelled inhabitant, retaining its typing and proof mode. -/
def Proves (P : Specification S) (Γ : List (Expr S)) (γ : Nat → Mode) (A : Expr S) : Prop :=
  ∃ p, HasType P Γ p A ∧ WellModed γ p .proof

namespace Proves
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B : Expr S} {s : S}

theorem rename (h : Proves P Γ γ A) (e : Embedding P Γ γ Δ δ) :
    Proves P Δ δ (A.rename e.names) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,e.typing hp,e.moded mp⟩

theorem of_var (hA : HasType P Γ A (.sort s)) :
    Proves P (A :: Γ) (modeCons .proof γ) (A.rename Nat.succ) :=
  ⟨_,.var hA,.var 0⟩

theorem apply_arrow (h : Proves P Γ γ (Expr.arrow .pp A B)) (ha : Proves P Γ γ A) :
    Proves P Γ γ B := by
  obtain ⟨p,hp,mp⟩ := h
  obtain ⟨a,ha,ma⟩ := ha
  exact ⟨_,hp.apply_arrow ha,.app mp ma⟩

theorem constLam {D : Expr S} {t : S} (h : Proves P Γ γ A)
    (hD : HasType P Γ D (.sort s)) (mD : WellModed γ D .data)
    (hpi : HasType P Γ (Expr.arrow .dp D A) (.sort t)) :
    Proves P Γ γ (Expr.arrow .dp D A) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,hp.constLam hD hpi,mD.constLam mp⟩
end Proves

namespace Transfer
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {A B D : Expr S} {s t : S}

theorem prove (h : Transfer P Γ γ A B) (hp : Proves P Γ γ A) : Proves P Γ γ B := by
  obtain ⟨t,ht,mt⟩ := h
  obtain ⟨p,hp,mp⟩ := hp
  exact ⟨_,by simpa only [Expr.instantiate_raise] using ht.instantiate hp,mt.instantiate mp⟩

theorem of_proves (hp : Proves P Γ γ B) (hA : HasType P Γ A (.sort s)) :
    Transfer P Γ γ A B := by
  obtain ⟨p,hp,mp⟩ := hp
  exact ⟨_,.weaken hp hA,mp.raise _⟩

theorem abstract (h : Transfer P Γ γ A B) (mA : WellModed γ A .data)
    (hpi : HasType P Γ (Expr.arrow .pp A B) (.sort s)) :
    Proves P Γ γ (Expr.arrow .pp A B) := by
  obtain ⟨p,hp,mp⟩ := h
  exact ⟨_,.abstraction hp hpi,.lam mA mp⟩

/-- An actual argument may be data or proof; its original application label is
retained, and the fresh proof input is inserted before the argument is used. -/
theorem apply_to {l : Label} {a : Expr S} (ha : HasType P Γ a A)
    (ma : WellModed γ a l.domain) (hl : l.result = .proof)
    (hpi : HasType P Γ (Expr.arrow l A B) (.sort s)) :
    Transfer P Γ γ (Expr.arrow l A B) B := by
  refine ⟨.app l (.var 0) (a.rename Nat.succ),?_,?_⟩
  · have hv := HasType.var hpi
    simp only [Expr.arrow_rename] at hv
    exact hv.apply_arrow (.weaken ha hpi)
  · have hv : WellModed (modeCons .proof γ) (.var 0 : Expr S) l.result :=
      hl.symm ▸ WellModed.var 0
    have hh : WellModed (modeCons .proof γ) (.app l (.var 0) (a.rename Nat.succ)) l.result :=
      .app hv (ma.raise .proof)
    simpa only [hl] using hh

 theorem apply_to_proof (ha : Proves P Γ γ A)
    (hpi : HasType P Γ (Expr.arrow .pp A B) (.sort s)) :
    Transfer P Γ γ (Expr.arrow .pp A B) B := by
  obtain ⟨a,ha,ma⟩ := ha
  exact apply_to ha ma rfl hpi
end Transfer
end

universe u
open Classical
variable {S : Type u} {P : Specification S}

theorem edge_profiles {I J : Set S} {b : Bool} (he : PrimaryEdge P I J b) :
    FeasibleProfile P I ∧ FeasibleProfile P J := by
  cases he with
  | inclusion hi hj _ => exact ⟨hi,hj⟩
  | domain h => exact ⟨h.domain,h.product⟩
  | codomain h => exact ⟨h.codomain,h.product⟩

/-- The converter-routing construction retains its finite admissible context,
its exact renaming of the original input, and the normal positive carried type. -/
def Carries (Γ : List (Expr S)) (γ : Nat → Mode) (T : Expr S) (J : Set S) : Prop :=
  ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧ ∃ U : Expr S,
    U.Target ∧ WellModed δ U .data ∧ SortedAt P Δ U J ∧
    Transfer P Δ δ (T.rename e.names) U

namespace WitnessFamily
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {T : Expr S} {I J : Set S}

include W in
theorem carry_edge (hv : ValidContext P Γ) (hc : ProofContext Γ γ)
    (hT : T.Target) (hm : WellModed γ T .data) (ht : SortedAt P Γ T I)
    {b : Bool} (he : PrimaryEdge P I J b) : Carries (P := P) Γ γ T J := by
  cases he with
  | inclusion hi hj hij =>
    obtain ⟨s,hs⟩ := hi.1
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,T,hT,hm,ht.mono hij.1,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using Transfer.refl (γ := γ) (ht s hs)
  | @codomain A B C htr =>
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨a,ha,b,hb,hab⟩ := htr.output ▸ hr
    let D := W.type A
    have hD : SortedAt P Γ D A := W.sorted A htr.domain
    have hU : SortedAt P Γ (Expr.arrow .dp D T) J := hD.arrow ht .dp (by rw [htr.output])
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,Expr.arrow .dp D T,
      hT.arrow (W.normal A htr.domain), (W.type_mode A htr.domain).arrow hm,hU,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using
      Transfer.positive (ht b hb) (hD a ha) hab (W.type_mode A htr.domain)
  | @domain A B C htr =>
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨a,ha,b,hb,hab⟩ := htr.output ▸ hr
    let F := W.type B
    have hF : SortedAt P Γ F B := W.sorted B htr.codomain
    have hConv : HasType P Γ (Expr.arrow .pp T F) (.sort r) := (ht a ha).arrow (hF b hb) hab
    let e : Embedding P Γ γ (Expr.arrow .pp T F :: Γ) (modeCons .proof γ) := Embedding.cons hConv .proof
    let W' := W.rename e
    let D := W'.type I
    let F' := W'.type B
    have hD : SortedAt P (Expr.arrow .pp T F :: Γ) D I := W'.sorted I htr.domain
    have hF' : SortedAt P (Expr.arrow .pp T F :: Γ) F' B := W'.sorted B htr.codomain
    have hU : SortedAt P (Expr.arrow .pp T F :: Γ) (Expr.arrow .dp D F') J :=
      hD.arrow hF' .dp (by rw [htr.output])
    have hFT : F'.Target := ⟨.terminal (W'.allData B htr.codomain), W'.normal B htr.codomain⟩
    refine ⟨_,_,e,hc.proof_cons hT,Expr.arrow .dp D F',hFT.arrow (W'.normal I htr.domain),
      (W'.type_mode I htr.domain).arrow (W'.type_mode B htr.codomain),hU,?_⟩
    exact (Transfer.converter hConv (ht a ha)).trans
      (Transfer.positive (hF' b hb) (hD a ha) hab (W'.type_mode I htr.domain))
      (e.typing (ht a ha)) (hF' b hb)

include W in
/-- Each negative edge resets the carried type to a fixed terminal, and is
followed by its own positive lift. Thus every converter domain stays positive. -/
theorem carry_path {b : Bool} (hp : SignedPath (PrimaryEdge P) I J b)
    (hI : FeasibleProfile P I) (hv : ValidContext P Γ) (hc : ProofContext Γ γ)
    (hT : T.Target) (hm : WellModed γ T .data) (ht : SortedAt P Γ T I) :
    Carries (P := P) Γ γ T J := by
  induction hp generalizing Γ γ T with
  | nil I =>
    obtain ⟨s,hs⟩ := hI.1
    refine ⟨Γ,γ,Embedding.refl hv γ,hc,T,hT,hm,ht,?_⟩
    simpa only [Embedding.refl,Expr.rename_id] using Transfer.refl (γ := γ) (ht s hs)
  | @cons I J K b c he hp ih =>
    obtain ⟨Δ,δ,e,hΔ,U,hU,mU,tU,tr⟩ := W.carry_edge hv hc hT hm ht he
    obtain ⟨Θ,θ,f,hΘ,V,hV,mV,tV,tr'⟩ := ih (W.rename e) (edge_profiles he).2 e.valid hΔ hU mU tU
    obtain ⟨s,hs⟩ := hI.1
    obtain ⟨t,ht'⟩ := (edge_profiles he).2.1
    have htr := (tr.rename f (e.typing (ht s hs))).trans tr'
      (f.typing (e.typing (ht s hs))) (f.typing (tU t ht'))
    refine ⟨Θ,θ,e.comp f,hΘ,V,hV,mV,tV,?_⟩
    simpa only [Embedding.comp,Expr.rename_comp] using htr

/-- Terminal-converter existence. Both terminal types are the original,
fixed witnesses; only legal renaming is applied. -/
theorem terminal_transfer {C : Set (Set S)} (hC : IsComponent (PrimaryEdge P) C)
    {I₁ J₁ K₁ I₂ J₂ K₂ : Set S}
    (h₁ : ProfileTriple P I₁ J₁ K₁) (hk₁ : K₁ ∈ C)
    (h₂ : ProfileTriple P I₂ J₂ K₂) (hi₂ : I₂ ∈ C)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      Transfer P Δ δ ((W.type J₁).rename e.names) ((W.type J₂).rename e.names) := by
  obtain ⟨b,hp⟩ := hC.connected hk₁ hi₂
  have route := SignedPath.cons (PrimaryEdge.codomain h₁) hp
  obtain ⟨Δ,δ,e,hΔ,U,hU,_mU,tU,tr⟩ := W.carry_path route h₁.codomain hv hc
    ⟨.terminal (W.allData J₁ h₁.codomain),W.normal J₁ h₁.codomain⟩
    (W.type_mode J₁ h₁.codomain) (W.sorted J₁ h₁.codomain)
  let W' := W.rename e
  obtain ⟨r,hr⟩ := h₂.product.1
  obtain ⟨a,ha,b,hb,hab⟩ := h₂.output ▸ hr
  have hF := W'.sorted J₂ h₂.codomain
  have hConv := (tU a ha).arrow (l := .pp) (hF b hb) hab
  let f : Embedding P Δ δ (Expr.arrow .pp U (W'.type J₂) :: Δ) (modeCons .proof δ) :=
    Embedding.cons hConv .proof
  obtain ⟨s,hs⟩ := h₁.codomain.1
  have hA := e.typing (W.sorted J₁ h₁.codomain s hs)
  have out := (tr.rename f hA).trans (Transfer.converter hConv (tU a ha))
    (f.typing hA) (f.typing (tU a ha))
  refine ⟨_,_,e.comp f,hΔ.proof_cons hU,?_⟩
  simpa only [Embedding.comp,W',WitnessFamily.rename,Expr.rename_comp,f,Embedding.cons] using out
end WitnessFamily

/-- The fixed terminals are exactly the codomains of the internal domain edges
of the logic SCC. This includes the chosen logical bottom. -/
def TerminalProfile (P : Specification S) (C : Set (Set S)) (J : Set S) : Prop :=
  ∃ I K, ProfileTriple P I J K ∧ I ∈ C ∧ K ∈ C

theorem TerminalProfile.feasible {C : Set (Set S)} {J : Set S}
    (h : TerminalProfile P C J) : FeasibleProfile P J := by
  obtain ⟨I,K,ht,_,_⟩ := h
  exact ht.codomain

namespace WitnessFamily
variable {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    {C : Set (Set S)}

/-- Previously constructed routes survive every new converter declaration. The
finite induction performs all context extensions before any logical input. -/
theorem finite_terminal_network (hC : IsComponent (PrimaryEdge P) C)
    (F : Finset (Set S × Set S))
    (hF : ∀ q ∈ F, TerminalProfile P C q.1 ∧ TerminalProfile P C q.2)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      ∀ q ∈ F, Transfer P Δ δ ((W.type q.1).rename e.names) ((W.type q.2).rename e.names) := by
  induction F using Finset.induction_on generalizing Γ γ with
  | empty => exact ⟨Γ,γ,Embedding.refl hv γ,hc,by simp⟩
  | @insert a F han ih =>
    obtain ⟨ha₁,ha₂⟩ := hF a (Finset.mem_insert_self _ _)
    obtain ⟨Δ,δ,e,hΔ,hs⟩ := ih W (fun q hq => hF q (Finset.mem_insert_of_mem hq)) hv hc
    obtain ⟨I₁,K₁,h₁,_hi₁,hk₁⟩ := ha₁
    obtain ⟨I₂,K₂,h₂,hi₂,_hk₂⟩ := ha₂
    obtain ⟨Θ,θ,f,hΘ,hnew⟩ := (W.rename e).terminal_transfer hC h₁ hk₁ h₂ hi₂ e.valid hΔ
    refine ⟨Θ,θ,e.comp f,hΘ,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hnew
    · obtain ⟨s,hsort⟩ := (hF q (Finset.mem_insert_of_mem hq)).1.feasible.1
      have ht := (hs q hq).rename f (e.typing (W.sorted q.1
        (hF q (Finset.mem_insert_of_mem hq)).1.feasible s hsort))
      simpa only [Embedding.comp,Expr.rename_comp] using ht

/-- One fixed finite legal context has every pairwise terminal transfer. -/
theorem terminal_network [Fintype S] (hC : IsComponent (PrimaryEdge P) C)
    (hv : ValidContext P Γ) (hc : ProofContext Γ γ) :
    ∃ Δ δ, ∃ e : Embedding P Γ γ Δ δ, ProofContext Δ δ ∧
      ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
        Transfer P Δ δ ((W.type J).rename e.names) ((W.type J').rename e.names) := by
  let F : Finset (Set S × Set S) := Finset.univ.filter
    (fun q => TerminalProfile P C q.1 ∧ TerminalProfile P C q.2)
  obtain ⟨Δ,δ,e,hΔ,hs⟩ := W.finite_terminal_network hC F
    (fun q hq => (Finset.mem_filter.mp hq).2) hv hc
  exact ⟨Δ,δ,e,hΔ,fun J J' hJ hJ' => hs (J,J') (by simp [F,hJ,hJ'])⟩
end WitnessFamily

/-- Uniform proof transport records open callbacks, not a meta-level implication
between propositions. Every operation returns an actual typed term. -/
def ProofParity {Γ : List (Expr S)} {γ : Nat → Mode}
    (W : WitnessFamily P Γ γ) (C : Set (Set S)) (A B : Expr S) (b : Bool) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
    match b with
    | false =>
      (Proves P Δ δ (A.rename e.names) → Proves P Δ δ (B.rename e.names)) ∧
      (∀ J, TerminalProfile P C J →
        Transfer P Δ δ (A.rename e.names) ((W.type J).rename e.names) →
        Transfer P Δ δ (B.rename e.names) ((W.type J).rename e.names))
    | true =>
      (∀ J, TerminalProfile P C J →
        Transfer P Δ δ (A.rename e.names) ((W.type J).rename e.names) →
        Proves P Δ δ (B.rename e.names)) ∧
      (∀ J, TerminalProfile P C J → Proves P Δ δ (A.rename e.names) →
        Transfer P Δ δ (B.rename e.names) ((W.type J).rename e.names))

namespace ProofParity
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {A B D : Expr S} {b : Bool} {s t r : S}

theorem refl : ProofParity W C A A false := by
  intro Δ δ e
  exact ⟨id,fun _ _ => id⟩

/-- Positive paths retain the literal data witness used by projection. -/
theorem positive (h : ProofParity W C A B b)
    (hB : HasType P Γ B (.sort s)) (hD : HasType P Γ D (.sort t))
    (mD : WellModed γ D .data) {d : Expr S}
    (hd : HasType P Γ d D) (md : WellModed γ d .data)
    (hpi : HasType P Γ (Expr.arrow .dp D B) (.sort r)) :
    ProofParity W C A (Expr.arrow .dp D B) b := by
  intro Δ δ e
  have hB' := e.typing hB
  have hD' := e.typing hD
  have hpi' : HasType P Δ (Expr.arrow .dp (D.rename e.names) (B.rename e.names)) (.sort r) := by
    simpa only [Expr.arrow_rename,Expr.rename] using e.typing hpi
  have hp := Transfer.apply_to (e.typing hd) (e.moded md) (l := .dp) rfl hpi'
  cases b with
  | false =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro ha
      simpa only [Expr.arrow_rename] using (hin ha).constLam hD' (e.moded mD) hpi'
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using hp.trans (hout J hJ ha) hpi' hB'
  | true =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using (hin J hJ ha).constLam hD' (e.moded mD) hpi'
    · intro J hJ ha
      simpa only [Expr.arrow_rename] using hp.trans (hout J hJ ha) hpi' hB'

/-- Each negative edge uses its fixed terminal; even/odd callbacks
are composed only with the predeclared terminal terms. -/
theorem negative (h : ProofParity W C A B b)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {J₀ : Set S} (hJ₀ : TerminalProfile P C J₀)
    (hB : HasType P Γ B (.sort s)) (mB : WellModed γ B .data)
    (hpi : HasType P Γ (Expr.arrow .pp B (W.type J₀)) (.sort r)) :
    ProofParity W C A (Expr.arrow .pp B (W.type J₀)) (!b) := by
  intro Δ δ e
  have hB' := e.typing hB
  obtain ⟨t₀,ht₀⟩ := hJ₀.feasible.1
  have hF₀ := e.typing (W.sorted J₀ hJ₀.feasible t₀ ht₀)
  have hpi' : HasType P Δ (Expr.arrow .pp (B.rename e.names) ((W.type J₀).rename e.names)) (.sort r) := by
    simpa only [Expr.arrow_rename,Expr.rename] using e.typing hpi
  have conv (J J' : Set S) (hJ : TerminalProfile P C J) (hJ' : TerminalProfile P C J') :
      Transfer P Δ δ ((W.type J).rename e.names) ((W.type J').rename e.names) := by
    obtain ⟨t,ht⟩ := hJ.feasible.1
    exact (τ J J' hJ hJ').rename e (W.sorted J hJ.feasible t ht)
  cases b with
  | false =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro J hJ ha
      obtain ⟨t,ht⟩ := hJ.feasible.1
      have hF := e.typing (W.sorted J hJ.feasible t ht)
      have hh := (hout J hJ ha).trans (conv J J₀ hJ hJ₀) hB' hF
      simpa only [Expr.arrow_rename] using hh.abstract (e.moded mB) hpi'
    · intro J hJ ha
      have hh := (Transfer.apply_to_proof (hin ha) hpi').trans (conv J₀ J hJ₀ hJ) hpi' hF₀
      simpa only [Expr.arrow_rename] using hh
  | true =>
    obtain ⟨hin,hout⟩ := h Δ δ e
    refine ⟨?_,?_⟩
    · intro ha
      simpa only [Expr.arrow_rename] using (hout J₀ hJ₀ ha).abstract (e.moded mB) hpi'
    · intro J hJ ha
      have hh := (Transfer.apply_to_proof (hin J hJ ha) hpi').trans (conv J₀ J hJ₀ hJ) hpi' hF₀
      simpa only [Expr.arrow_rename] using hh
end ProofParity

/-- A continuation is tested after every legal extension; callbacks are actual
open terms with one proof input, not arbitrary functions on inhabitation. -/
def Continuation {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ)
    J, TerminalProfile P C J →
    Transfer P Δ δ (Q.rename e.names) ((W.type J).rename e.names) →
    Proves P Δ δ ((W.type J).rename e.names)

/-- The extraction property proved for sorted stable telescopes. It is not an
extra PTS rule: the following constructors explicitly build its proof terms. -/
def StableExtraction {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (Q : Expr S) : Prop :=
  ∀ (Δ : List (Expr S)) (δ : Nat → Mode) (e : Embedding P Γ γ Δ δ),
    Continuation (W.rename e) C (Q.rename e.names) → Proves P Δ δ (Q.rename e.names)

namespace Continuation
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {Q : Expr S}
theorem rename (h : Continuation W C Q) (e : Embedding P Γ γ Δ δ) :
    Continuation (W.rename e) C (Q.rename e.names) := by
  intro Θ θ f J hJ ht
  have hh := h Θ θ (e.comp f) J hJ
  simp only [WitnessFamily.rename,Expr.rename_comp] at ht ⊢
  exact hh ht
end Continuation

namespace Transfer
variable {Γ : List (Expr S)} {γ : Nat → Mode} {A B : Expr S} {s t : S}

/-- Project a dependent product at its newly opened raw argument, retaining the
argument's actual data/proof label. -/
theorem project_pi {l : Label} (hA : HasType P Γ A (.sort s))
    (hpi : HasType P Γ (.pi l A B) (.sort t)) (hl : l.result = .proof) :
    Transfer P (A :: Γ) (modeCons l.domain γ) ((Expr.pi l A B).rename Nat.succ) B := by
  let hpi' := HasType.weaken hpi hA
  have hv := HasType.var hpi'
  have hx := HasType.weaken (HasType.var hA) hpi'
  have hterm := HasType.application hv hx
  have heq : (((B.rename (Expr.liftRen Nat.succ)).rename (Expr.liftRen Nat.succ)).instantiate (.var 1)) =
      B.rename Nat.succ := by
    simp only [Expr.instantiate,Expr.subst_rename,Expr.rename_comp]
    rw [← Expr.subst_var (B.rename Nat.succ),Expr.subst_rename]
    congr 1
    funext n
    cases n <;> rfl
  have hm : WellModed (modeCons .proof (modeCons l.domain γ))
      (.app l (.var 0) (.var 1) : Expr S) l.result :=
    .app (hl.symm ▸ WellModed.var 0) (.var 1)
  exact ⟨_,by simpa only [Expr.rename,heq] using hterm,by simpa only [hl] using hm⟩
end Transfer

namespace StableExtraction
variable {Γ Δ : List (Expr S)} {γ δ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {Q A B : Expr S} {s t : S}

theorem rename (h : StableExtraction W C Q) (e : Embedding P Γ γ Δ δ) :
    StableExtraction (W.rename e) C (Q.rename e.names) := by
  intro Θ θ f hk
  have hk' : Continuation (W.rename (e.comp f)) C (Q.rename (e.comp f).names) := by
    simpa only [Continuation,Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hk
  simpa only [Embedding.comp,Expr.rename_comp] using h Θ θ (e.comp f) hk'

theorem terminal {J : Set S} (hJ : TerminalProfile P C J) : StableExtraction W C (W.type J) := by
  intro Δ δ e hk
  obtain ⟨s,hs⟩ := hJ.feasible.1
  have hF := e.typing (W.sorted J hJ.feasible s hs)
  have ht : Transfer P Δ δ ((W.type J).rename e.names) ((W.type J).rename e.names) := .refl hF
  have hr := hk Δ δ (Embedding.refl e.valid δ) J hJ
  simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using hr (by
    simpa only [WitnessFamily.rename,Embedding.refl,Expr.rename_id] using ht)

/-- Dependent telescope step. The continuation is threaded under the raw binder;
the raw projection supplies the callback at exactly that locally opened value. -/
theorem product {l : Label} (hA : HasType P Γ A (.sort s))
    (mA : WellModed γ A .data) (hpi : HasType P Γ (.pi l A B) (.sort t))
    (hl : l.result = .proof)
    (hB : StableExtraction (W.rename (Embedding.cons hA l.domain)) C B) :
    StableExtraction W C (.pi l A B) := by
  intro Δ δ e hk
  let hA' := e.typing hA
  let d : Embedding P Δ δ (A.rename e.names :: Δ) (modeCons l.domain δ) :=
    Embedding.cons hA' l.domain
  have hpi' : HasType P Δ (.pi l (A.rename e.names) (B.rename (Expr.liftRen e.names))) (.sort t) :=
    e.typing hpi
  have hp := Transfer.project_pi (γ := δ) hA' hpi' hl
  have hb : Proves P (A.rename e.names :: Δ) (modeCons l.domain δ) (B.rename (Expr.liftRen e.names)) := by
    apply hB _ _ (e.lift hA l.domain)
    intro Θ θ f J hJ hc
    have hfpi := HasType.weaken hpi' hA'
    have hp' := hp.rename f hfpi
    obtain ⟨a,bs,c,ha,hbody,hr,_⟩ := hpi'.generation_pi
    have hbody' : HasType P Θ ((B.rename (Expr.liftRen e.names)).rename f.names) (.sort bs) := by
      simpa only [Expr.rename] using f.typing hbody
    have hcb := hp'.trans hc (f.typing hfpi) hbody'
    change Transfer P Θ θ ((((Expr.pi l A B).rename e.names).rename Nat.succ).rename f.names)
      (((((W.rename (Embedding.cons hA l.domain)).rename (e.lift hA l.domain)).type J)).rename f.names) at hcb
    have hres := hk Θ θ (d.comp f) J hJ
    have hcb' : Transfer P Θ θ ((Expr.pi l A B).rename e.names |>.rename (d.comp f).names)
        (((W.rename e).type J).rename (d.comp f).names) := by
      simpa only [Embedding.comp,Embedding.lift,Embedding.cons,d,
        WitnessFamily.rename,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,
        Function.comp_def] using hcb
    simpa only [Embedding.comp,Embedding.lift,Embedding.cons,d,
      WitnessFamily.rename,Expr.rename_comp,Expr.liftRen,PureTypeSystem.Expr.liftRen,
      Function.comp_def] using hres hcb' 
  obtain ⟨b,hb,mb⟩ := hb
  have ml : WellModed δ (.lam l (A.rename e.names) b) l.result :=
    .lam (e.moded mA) (by simpa only [hl] using mb)
  exact ⟨_,.abstraction hb hpi',by simpa only [hl] using ml⟩

/-- Constant arrows are the special telescope step used by every path edge. -/
theorem arrow {l : Label} (hA : HasType P Γ A (.sort s))
    (mA : WellModed γ A .data) (hpi : HasType P Γ (Expr.arrow l A B) (.sort t))
    (hl : l.result = .proof) (hB : StableExtraction W C B) :
    StableExtraction W C (Expr.arrow l A B) :=
  product hA mA hpi hl (hB.rename (Embedding.cons hA l.domain))

end StableExtraction

namespace ProofParity
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {A B : Expr S} {s t : S}

theorem into (h : ProofParity W C A B false) (hA : HasType P Γ A (.sort s)) :
    Transfer P Γ γ A B := by
  have hp := (h _ _ (Embedding.cons hA .proof)).1 (Proves.of_var hA)
  exact hp

/-- Stable even-path retraction, including dependent stable telescopes. -/
theorem down (h : ProofParity W C A B false) (hs : StableExtraction W C A)
    (hB : HasType P Γ B (.sort t)) : Transfer P Γ γ B A := by
  let d : Embedding P Γ γ (B :: Γ) (modeCons .proof γ) := Embedding.cons hB .proof
  apply hs _ _ d
  intro Δ δ e J hJ hc
  have hout := (h Δ δ (d.comp e)).2 J hJ
  have hc' : Transfer P Δ δ (A.rename (d.comp e).names) ((W.type J).rename (d.comp e).names) := by
    simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using hc
  have hp := (Proves.of_var (γ := γ) hB).rename e
  have hp' : Proves P Δ δ (B.rename (d.comp e).names) := by
    simpa only [Embedding.comp,d,Embedding.cons,Expr.rename_comp] using hp
  simpa only [Embedding.comp,WitnessFamily.rename,Expr.rename_comp] using (hout hc').prove hp'
end ProofParity

/-- Fixed hygienic wrapper syntax. The code is selected once from a path, never
reselected when an input is substituted or its sorting profile grows. -/
inductive ProofWrapper (S : Type u)
  | identity
  | positive : ProofWrapper S → Expr S → ProofWrapper S
  | negative : ProofWrapper S → Expr S → ProofWrapper S

namespace ProofWrapper

def apply : ProofWrapper S → Expr S → Expr S
  | .identity,T => T
  | .positive R D,T => Expr.arrow .dp D (R.apply T)
  | .negative R F,T => Expr.arrow .pp (R.apply T) F

def rename (ρ : Nat → Nat) : ProofWrapper S → ProofWrapper S
  | .identity => .identity
  | .positive R D => .positive (R.rename ρ) (D.rename ρ)
  | .negative R F => .negative (R.rename ρ) (F.rename ρ)

def subst (σ : Nat → Expr S) : ProofWrapper S → ProofWrapper S
  | .identity => .identity
  | .positive R D => .positive (R.subst σ) (D.subst σ)
  | .negative R F => .negative (R.subst σ) (F.subst σ)

theorem apply_rename (R : ProofWrapper S) (T : Expr S) (ρ : Nat → Nat) :
    (R.apply T).rename ρ = (R.rename ρ).apply (T.rename ρ) := by
  induction R <;> simp_all only [apply,rename,Expr.arrow_rename]

theorem apply_subst (R : ProofWrapper S) (T : Expr S) (σ : Nat → Expr S) :
    (R.apply T).subst σ = (R.subst σ).apply (T.subst σ) := by
  induction R <;> simp_all only [apply,subst,Expr.arrow_subst]

def containsNegative : ProofWrapper S → Bool
  | .identity => false
  | .positive R _ => R.containsNegative
  | .negative _ _ => true

theorem rename_id (R : ProofWrapper S) : R.rename id = R := by
  induction R <;> simp_all only [rename,Expr.rename_id]

theorem rename_comp (R : ProofWrapper S) (ρ σ : Nat → Nat) :
    (R.rename σ).rename ρ = R.rename (ρ ∘ σ) := by
  induction R <;> simp_all only [rename,Expr.rename_comp]

theorem instantiate_raise (R : ProofWrapper S) (a : Expr S) :
    (R.rename Nat.succ).subst (Expr.single a) = R := by
  induction R <;> simp_all only [rename,subst,Expr.subst_lift_single]

/-- A path certificate retaining exactly its terminals, witness types and edge
roles. Inclusion is a literal identity; there is no type-level cast. -/
inductive Formed {Γ : List (Expr S)} {γ : Nat → Mode} (W : WitnessFamily P Γ γ)
    (C : Set (Set S)) (I : Set S) : Set S → Bool → ProofWrapper S → Prop
  | identity : Formed W C I I false .identity
  | inclusion {J K b R} : Formed W C I J b R → K ⊆ J → Formed W C I K b R
  | positive {A J K b R} : Formed W C I J b R → ProfileTriple P A J K →
      Formed W C I K b (.positive R (W.type A))
  | negative {J B K b R} : Formed W C I J b R → ProfileTriple P J B K → J ∈ C → K ∈ C →
      Formed W C I K (!b) (.negative R (W.type B))

namespace Formed
variable {Γ : List (Expr S)} {γ : Nat → Mode} {W : WitnessFamily P Γ γ}
    {C : Set (Set S)} {I J K : Set S} {a b : Bool} {R : ProofWrapper S}

theorem rename {Δ : List (Expr S)} {δ : Nat → Mode}
    (h : Formed W C I J b R) (e : Embedding P Γ γ Δ δ) :
    Formed (W.rename e) C I J b (R.rename e.names) := by
  induction h with
  | identity => exact .identity
  | inclusion h hh ih => exact ih.inclusion hh
  | positive h ht ih => exact ih.positive ht
  | negative h ht hi hk ih => exact ih.negative ht hi hk

theorem edge (h : Formed W C I J a R) (he : PrimaryEdge P J K b) (hJ : J ∈ C) (hK : K ∈ C) :
    ∃ R', Formed W C I K (Bool.xor a b) R' := by
  cases he with
  | inclusion hJ' hK' hsub => simpa only [Bool.xor_false] using Exists.intro R (h.inclusion hsub.1)
  | domain ht => simpa only [Bool.xor_true] using Exists.intro _ (h.negative ht hJ hK)
  | codomain ht => simpa only [Bool.xor_false] using Exists.intro _ (h.positive ht)

theorem path (h : Formed W C I J a R)
    (hp : SignedPath (fun x y s => PrimaryEdge P x y s ∧ x ∈ C ∧ y ∈ C) J K b) :
    ∃ R', Formed W C I K (Bool.xor a b) R' := by
  induction hp generalizing a R with
  | nil _ => simpa only [Bool.xor_false] using Exists.intro R h
  | @cons J K L b c he hp ih =>
    obtain ⟨R',hr⟩ := h.edge he.1 he.2.1 he.2.2
    obtain ⟨R'',hr'⟩ := ih hr
    exact ⟨R'',by simpa only [Bool.xor_assoc] using hr'⟩

/-- The fixed code has the actual profile sorting, mode, and parity operations. -/
theorem sound (h : Formed W C I J b R)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {T : Expr S} (ht : SortedAt P Γ T I) (mt : WellModed γ T .data) :
    SortedAt P Γ (R.apply T) J ∧ WellModed γ (R.apply T) .data ∧
      ProofParity W C T (R.apply T) b := by
  induction h with
  | identity => exact ⟨ht,mt,ProofParity.refl⟩
  | inclusion h hsub ih => exact ⟨ih.1.mono hsub,ih.2⟩
  | @positive A J K b R h htr ih =>
    have hsorted : SortedAt P Γ (Expr.arrow .dp (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow ih.1 .dp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht,hst⟩ := htr.output ▸ hr
    exact ⟨hsorted,(W.type_mode A htr.domain).arrow ih.2.1,
      ih.2.2.positive (ih.1 t ht) (W.sorted A htr.domain s hs)
        (W.type_mode A htr.domain) (W.typed A htr.domain) (W.value_mode A htr.domain) (hsorted r hr)⟩
  | @negative J B K b R h htr hJ hK ih =>
    have hsorted : SortedAt P Γ (Expr.arrow .pp (R.apply T) (W.type B)) K :=
      ih.1.arrow (W.sorted B htr.codomain) .pp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht,hst⟩ := htr.output ▸ hr
    exact ⟨hsorted,ih.2.1.arrow (W.type_mode B htr.codomain),
      ih.2.2.negative τ ⟨J,K,htr,hJ,hK⟩ (ih.1 s hs) ih.2.1 (hsorted r hr)⟩

/-- Every code preserves stable extraction; a negative-containing code creates
it even for an initially arbitrary data type. -/
theorem stable (h : Formed W C I J b R)
    (τ : ∀ J J', TerminalProfile P C J → TerminalProfile P C J' →
      Transfer P Γ γ (W.type J) (W.type J'))
    {T : Expr S} (ht : SortedAt P Γ T I) (mt : WellModed γ T .data) :
    (StableExtraction W C T → StableExtraction W C (R.apply T)) ∧
      (R.containsNegative = true → StableExtraction W C (R.apply T)) := by
  induction h with
  | identity => exact ⟨id,by simp only [containsNegative,Bool.false_eq_true]; tauto⟩
  | inclusion h hsub ih => exact ih
  | @positive A J K b R h htr ih =>
    obtain ⟨htR,mtR,hpar⟩ := h.sound τ ht mt
    have hsorted : SortedAt P Γ (Expr.arrow .dp (W.type A) (R.apply T)) K :=
      (W.sorted A htr.domain).arrow htR .dp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht',hst⟩ := htr.output ▸ hr
    have step : StableExtraction W C (R.apply T) →
        StableExtraction W C ((ProofWrapper.positive R (W.type A)).apply T) :=
      StableExtraction.arrow (W.sorted A htr.domain s hs) (W.type_mode A htr.domain) (hsorted r hr) rfl
    exact ⟨fun hp => step (ih.1 hp),fun hn => step (ih.2 hn)⟩
  | @negative J B K b R h htr hJ hK ih =>
    obtain ⟨htR,mtR,hpar⟩ := h.sound τ ht mt
    have hsorted : SortedAt P Γ (Expr.arrow .pp (R.apply T) (W.type B)) K :=
      htR.arrow (W.sorted B htr.codomain) .pp (by rw [htr.output])
    obtain ⟨r,hr⟩ := htr.product.1
    obtain ⟨s,hs,t,ht',hst⟩ := htr.output ▸ hr
    have hx : StableExtraction W C ((ProofWrapper.negative R (W.type B)).apply T) :=
      StableExtraction.arrow (htR s hs) mtR (hsorted r hr) rfl
        (StableExtraction.terminal ⟨J,K,htr,hJ,hK⟩)
    exact ⟨fun _ => hx,fun _ => hx⟩

end Formed
end ProofWrapper
end PureTypeSystem.Labelled

end OAI
