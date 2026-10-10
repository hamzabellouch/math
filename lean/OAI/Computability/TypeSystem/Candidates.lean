import OAI.Computability.TypeSystem.Contexts

namespace OAI

namespace PureTypeSystem

universe u

namespace Candidates

variable {S : Type u} {P : Specification S} (Ω : ContextTower P)

/-- Source actual types: a normal sorted expression, or a literal sort. -/
def ActualType (T : Expr S) : Prop :=
  (Normal T ∧ ∃ s, Ω.HasType T (.sort s)) ∨ ∃ s, T = .sort s

def Top (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ StronglyNormalizing M}

/-- Tests follow the exact normal successive types, not other typings. -/
inductive TestedStack : Expr S → List (Expr S) → Prop
  | nil (T) : TestedStack T []
  | cons {D E n ns} : n ∈ Top Ω D →
      TestedStack (E.instantiate n).normalForm ns → TestedStack (.pi D E) (n :: ns)

def Ground (T : Expr S) : Set (Expr S) :=
  {M | Ω.HasType M T ∧ ∀ ns, TestedStack Ω T ns → StronglyNormalizing (M.apps ns)}

namespace TestedStack

variable {Ω} {T : Expr S} {ns : List (Expr S)}

theorem sn (h : TestedStack Ω T ns) : StronglyNormalizingArgs ns := by
  induction h with
  | nil => exact .nil
  | cons hn _ ih => exact .cons hn.2 ih

theorem forall_sn (h : TestedStack Ω T ns) : ∀ n ∈ ns, StronglyNormalizing n := by
  induction h with
  | nil => simp
  | cons hn _ ih =>
      intro n hn'
      rcases List.mem_cons.mp hn' with rfl | hm
      · exact hn.2
      · exact ih n hm

end TestedStack

variable {Ω} {T M : Expr S}

theorem ground_le_top : Ground Ω T ⊆ Top Ω T := by
  intro M h
  exact ⟨h.1, h.2 [] (.nil T)⟩

theorem sort_ground_eq_top (s : S) : Ground Ω (.sort s) = Top Ω (.sort s) := by
  apply Set.Subset.antisymm ground_le_top
  intro M h
  refine ⟨h.1, ?_⟩
  intro ns hs
  cases hs
  exact h.2

theorem var_ground (n : Nat) (h : Ω.HasType (.var n) T) : .var n ∈ Ground Ω T :=
  ⟨h, fun _ hs => StronglyNormalizing.var_apps n hs.sn⟩

theorem ground_application (hw : SystemWeaklyNormalizing P) {D E n : Expr S}
    (h : M ∈ Ground Ω (.pi D E)) (hn : n ∈ Top Ω D) :
    .app M n ∈ Ground Ω (E.instantiate n).normalForm := by
  refine ⟨(h.1.application hn.1).normalize_type hw, ?_⟩
  intro ns hs
  exact h.2 (n :: ns) (.cons hn hs)

/-- Head expansion, with exact typing and SN of every annotation/spine component. -/
def ExpansionClosed (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop :=
  ∀ (D b n : Expr S) (ns : List (Expr S)),
    Ω.HasType ((Expr.app (.lam D b) n).apps ns) T →
    StronglyNormalizing D → StronglyNormalizing b → StronglyNormalizing n →
    StronglyNormalizingArgs ns → (b.instantiate n).apps ns ∈ C →
    (Expr.app (.lam D b) n).apps ns ∈ C

structure IsCandidate (Ω : ContextTower P) (T : Expr S) (C : Set (Expr S)) : Prop where
  lower : Ground Ω T ⊆ C
  upper : C ⊆ Top Ω T
  expansion : ExpansionClosed Ω T C

theorem top_candidate : IsCandidate Ω T (Top Ω T) where
  lower := ground_le_top
  upper := Set.Subset.rfl
  expansion := fun _ _ _ _ ht hD hb hn hns hc =>
    ⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.2⟩

/-- The bounded intersection makes the empty meet the typed top. -/
def Meet (Ω : ContextTower P) (T : Expr S) (Cs : Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω T ∧ ∀ C ∈ Cs, M ∈ C}

theorem meet_candidate {Cs : Set (Set (Expr S))}
    (hCs : ∀ C ∈ Cs, IsCandidate Ω T C) : IsCandidate Ω T (Meet Ω T Cs) where
  lower := fun _ h => ⟨ground_le_top h, fun C hC => (hCs C hC).lower h⟩
  upper := fun _ h => h.1
  expansion := by
    intro D b n ns ht hD hb hn hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb hn hns hc.1.2⟩, ?_⟩
    intro C hC
    exact (hCs C hC).expansion D b n ns ht hD hb hn hns (hc.2 C hC)

def Bottom (Ω : ContextTower P) (T : Expr S) : Set (Expr S) :=
  Meet Ω T {C | IsCandidate Ω T C}

theorem bottom_candidate : IsCandidate Ω T (Bottom Ω T) :=
  meet_candidate (fun _ h => h)

theorem bottom_le {C : Set (Expr S)} (hC : IsCandidate Ω T C) : Bottom Ω T ⊆ C :=
  fun _ h => h.2 C hC

/-- Arbitrary indexed product tests. -/
def ProductTest (Ω : ContextTower P) (D E : Expr S) (A : Set (Expr S))
    (Cs : Expr S → Set (Set (Expr S))) : Set (Expr S) :=
  {M | M ∈ Top Ω (.pi D E) ∧ ∀ n ∈ A, ∀ C ∈ Cs n, Expr.app M n ∈ C}

theorem productTest_candidate (hw : SystemWeaklyNormalizing P)
    {D E : Expr S} {A : Set (Expr S)} {Cs : Expr S → Set (Set (Expr S))}
    (hA : A ⊆ Top Ω D)
    (hCs : ∀ n ∈ A, ∀ C ∈ Cs n, IsCandidate Ω (E.instantiate n).normalForm C) :
    IsCandidate Ω (.pi D E) (ProductTest Ω D E A Cs) where
  lower := by
    intro M h
    refine ⟨ground_le_top h, ?_⟩
    intro n hn C hC
    exact (hCs n hn C hC).lower (ground_application hw h (hA hn))
  upper := fun _ h => h.1
  expansion := by
    intro D' b a ns ht hD hb ha hns hc
    refine ⟨⟨ht, StronglyNormalizing.head_expansion hD hb ha hns hc.1.2⟩, ?_⟩
    intro n hn C hC
    have ht' := (ht.application (hA hn).1).normalize_type hw
    have hsn : StronglyNormalizingArgs (ns ++ [n]) := by
      apply StronglyNormalizingArgs.of_forall
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hns.of_mem hx
      · have he : x = n := List.mem_singleton.mp hx
        exact he.symm ▸ (hA hn).2
    have hc' := hc.2 n hn C hC
    have he : (Expr.app (.lam D' b) a).apps (ns ++ [n]) =
        .app ((Expr.app (.lam D' b) a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    have he' : (b.instantiate a).apps (ns ++ [n]) = .app ((b.instantiate a).apps ns) n := by
      simp only [Expr.apps_append, Expr.apps]
    rw [← he] at ht'
    rw [← he'] at hc'
    rw [← he]
    exact (hCs n hn C hC).expansion D' b a (ns ++ [n]) ht' hD hb ha hsn hc'

end Candidates

end PureTypeSystem

namespace PureTypeSystem.Candidates
universe u
open Classical
variable {S : Type u} {P : Specification S} (Ω : ContextTower P) (T : Expr S)

abbrev Candidate := {X : Set (Expr S) // IsCandidate Ω T X}

noncomputable instance : InfSet (Candidate Ω T) where
  sInf Cs := ⟨Meet Ω T (Subtype.val '' Cs), meet_candidate (by
    rintro X ⟨x,_,rfl⟩
    exact x.property)⟩

noncomputable instance : CompleteLattice (Candidate Ω T) := completeLatticeOfInf _ (by
  intro Cs
  constructor
  · intro x hx M hM
    exact hM.2 x.val ⟨x,hx,rfl⟩
  · intro x hx M hM
    refine ⟨x.property.upper hM,?_⟩
    rintro X ⟨y,hy,rfl⟩
    exact hx hy hM)

/-- Changing coordinate order changes no candidate sets. -/
def SignedCandidate (b : Bool) : Type u := if b then (Candidate Ω T)ᵒᵈ else Candidate Ω T

noncomputable instance (b : Bool) : CompleteLattice (SignedCandidate Ω T b) := by
  cases b with
  | false => exact inferInstanceAs (CompleteLattice (Candidate Ω T))
  | true => exact inferInstanceAs (CompleteLattice (Candidate Ω T)ᵒᵈ)

namespace SignedCandidate
variable {Ω T} {b : Bool}

def set (X : SignedCandidate Ω T b) : Set (Expr S) := by
  cases b <;> exact X.val

def wrap (X : Candidate Ω T) : SignedCandidate Ω T b := by
  cases b <;> exact X

@[simp] theorem set_wrap (X : Candidate Ω T) : (wrap (b := b) X).set = X.val := by
  cases b <;> rfl

theorem candidate (X : SignedCandidate Ω T b) : IsCandidate Ω T X.set := by
  cases b <;> exact X.property

theorem order (X Y : SignedCandidate Ω T b) :
    X ≤ Y ↔ if b then Y.set ⊆ X.set else X.set ⊆ Y.set := by
  cases b <;> rfl

theorem ext {X Y : SignedCandidate Ω T b} (h : X.set = Y.set) : X = Y := by
  cases b <;> exact Subtype.ext h
end SignedCandidate
end PureTypeSystem.Candidates

end OAI
