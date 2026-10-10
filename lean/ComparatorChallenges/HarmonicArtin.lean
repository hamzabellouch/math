import Mathlib

namespace OAI

namespace HarmonicArtin

universe u

variable {S : Type u}

def alternating (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n

def braidRelators (M : CoxeterMatrix S) : Set (FreeGroup S) :=
  Set.range fun st : S × S =>
    alternating st.1 st.2 (M st.1 st.2) *
      (alternating st.2 st.1 (M st.1 st.2))⁻¹

abbrev Artin (M : CoxeterMatrix S) := PresentedGroup (braidRelators M)

def generator (M : CoxeterMatrix S) (s : S) : Artin M := PresentedGroup.of s

def coxeterParabolic (M : CoxeterMatrix S) (T : Set S) : Subgroup M.Group :=
  Subgroup.closure (M.simple '' T)

def IsSpherical (M : CoxeterMatrix S) (T : Set S) : Prop :=
  Finite (coxeterParabolic M T)

abbrev SphericalType (M : CoxeterMatrix S) := {T : Set S // IsSpherical M T}

abbrev LiftedCell (M : CoxeterMatrix S) := Artin M × SphericalType M

def wordArtin (M : CoxeterMatrix S) (w : List S) : Artin M :=
  (w.map (generator M)).prod

def wordCoxeter (M : CoxeterMatrix S) (w : List S) : M.Group :=
  (w.map M.simple).prod

def LiftedFace (M : CoxeterMatrix S) (a b : LiftedCell M) : Prop :=
  a.2.1 ⊆ b.2.1 ∧ ∃ w : List S,
    (∀ s ∈ w, s ∈ b.2.1) ∧
    M.toCoxeterSystem.length (wordCoxeter M w) = w.length ∧
    (∀ v : coxeterParabolic M a.2.1,
      M.toCoxeterSystem.length (wordCoxeter M w) ≤
        M.toCoxeterSystem.length (wordCoxeter M w * v)) ∧
    a.1 = b.1 * wordArtin M w

instance (M : CoxeterMatrix S) : Preorder (LiftedCell M) where
  le := Relation.ReflTransGen (LiftedFace M)
  le_refl _ := Relation.ReflTransGen.refl
  le_trans _ _ _ := Relation.ReflTransGen.trans

noncomputable def SalvettiCover (M : CoxeterMatrix S) : TopCat :=
  SSet.toTop.obj (CategoryTheory.nerve (LiftedCell M))

/-- The full lifted spherical-cell realization is contractible for every
Coxeter matrix with finitely many standard generators. -/
theorem salvetti_cover_contractible [Finite S] (M : CoxeterMatrix S) :
    ContractibleSpace (SalvettiCover M) := by
  sorry

end HarmonicArtin

end OAI
