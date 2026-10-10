import Mathlib.Data.Int.LeastGreatest
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Tactic

namespace OAI

/-!
# Integer filtration degree and initial forms

Section 3 uses an exhaustive separated increasing filtration indexed by all
integers, including negative integers.  These generic lemmas prove that every
nonzero element has a least layer and that its image modulo the preceding layer
is nonzero.  They do not assume any coordinate obstruction or associated-graded
presentation.
-/

namespace StableCoordinate
namespace IntegerFiltration

/-- The integer degree is the infimum of the layers containing an element.
The lemmas below show that for a nonzero element this infimum is attained. -/
noncomputable def degree {A : Type*} (F : ℤ → Set A) (x : A) : ℤ :=
  sInf {d : ℤ | x ∈ F d}

/-- A least layer computes the filtration degree. -/
theorem degree_eq_of_least {A : Type*} (F : ℤ → Set A) {x : A} {d : ℤ}
    (hd : x ∈ F d) (hleast : ∀ e : ℤ, x ∈ F e → d ≤ e) :
    degree F x = d := by
  exact IsLeast.csInf_eq ⟨hd, hleast⟩

section LeastDegree

variable {A : Type*} [Zero A]

/-- An exhaustive separated increasing integer filtration gives every nonzero
object a genuine least degree, not merely an infimum or a natural-number degree. -/
theorem exists_least_index (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    ∃ d : ℤ, x ∈ F d ∧ ∀ e : ℤ, x ∈ F e → d ≤ e := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : ℤ, x ∉ F b := by
    by_contra habs
    push Not at habs
    exact hx (hseparated x habs)
  apply Int.exists_least_of_bdd _ (hexhaustive x)
  refine ⟨b + 1, fun e he => ?_⟩
  have hnot : ¬ e ≤ b := fun heb => hb (hmono heb he)
  omega

/-- In particular the initial form of a nonzero element is represented in one
layer but not the preceding layer. -/
theorem exists_initial_index (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    ∃ d : ℤ, x ∈ F d ∧ x ∉ F (d - 1) := by
  obtain ⟨d, hd, hleast⟩ := exists_least_index F hmono hexhaustive hseparated hx
  refine ⟨d, hd, fun hprev => ?_⟩
  have := hleast (d - 1) hprev
  omega

omit [Zero A] in
/-- Such an initial index is unique. -/
theorem initial_index_unique (F : ℤ → Set A) (hmono : Monotone F)
    {x : A} {d e : ℤ} (hd : x ∈ F d) (hd' : x ∉ F (d - 1))
    (he : x ∈ F e) (he' : x ∉ F (e - 1)) : d = e := by
  have hde : d ≤ e := by
    by_contra h
    exact hd' (hmono (by omega : e ≤ d - 1) he)
  have hed : e ≤ d := by
    by_contra h
    exact he' (hmono (by omega : d ≤ e - 1) hd)
  exact le_antisymm hde hed

/-- The degree of a nonzero element is an attained least index. -/
theorem degree_spec (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    x ∈ F (degree F x) ∧ ∀ e : ℤ, x ∈ F e → degree F x ≤ e := by
  obtain ⟨d, hd, hleast⟩ := exists_least_index F hmono hexhaustive hseparated hx
  rw [degree_eq_of_least F hd hleast]
  exact ⟨hd, hleast⟩

/-- Membership in a filtration layer is equivalent to the integer degree bound. -/
theorem mem_iff_degree_le (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) (e : ℤ) :
    x ∈ F e ↔ degree F x ≤ e := by
  obtain ⟨hd, hleast⟩ := degree_spec F hmono hexhaustive hseparated hx
  exact ⟨hleast e, fun he => hmono he hd⟩

/-- The preceding layer misses every nonzero element. -/
theorem not_mem_degree_sub_one (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) : x ∉ F (degree F x - 1) := by
  intro h
  have := (degree_spec F hmono hexhaustive hseparated hx).2 _ h
  omega

/-- The degree is characterized by membership in a layer and failure of
membership in the immediately preceding layer. -/
theorem degree_eq_iff_initial (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) (d : ℤ) :
    degree F x = d ↔ x ∈ F d ∧ x ∉ F (d - 1) := by
  constructor
  · rintro rfl
    exact ⟨(degree_spec F hmono hexhaustive hseparated hx).1,
      not_mem_degree_sub_one F hmono hexhaustive hseparated hx⟩
  · rintro ⟨hd, hprev⟩
    exact initial_index_unique F hmono
      (degree_spec F hmono hexhaustive hseparated hx).1
      (not_mem_degree_sub_one F hmono hexhaustive hseparated hx) hd hprev

/-- Being outside the zeroth layer is exactly positivity of filtration degree. -/
theorem degree_pos_iff (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    0 < degree F x ↔ x ∉ F 0 := by
  rw [mem_iff_degree_le F hmono hexhaustive hseparated hx 0]
  exact lt_iff_not_ge

end LeastDegree

section InitialForm

variable {K A : Type*} [Ring K] [AddCommGroup A] [Module K A]

/-- A representative in the first possible layer is nonzero in the quotient by
its preceding layer.  This is the nonvanishing needed for an initial form. -/
theorem initial_form_ne_zero (F : ℤ → Submodule K A) {d : ℤ} {x : A}
    (hx : x ∈ F d) (hxprev : x ∉ F (d - 1)) :
    (Submodule.Quotient.mk ⟨x, hx⟩ :
      (F d) ⧸ (F (d - 1)).comap (F d).subtype) ≠ 0 := by
  intro h
  have hmem : (⟨x, hx⟩ : F d) ∈ (F (d - 1)).comap (F d).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  exact hxprev hmem

/-- Separation phrased as a lattice intersection implies elementwise separation. -/
theorem separated_of_iInf_eq_bot (F : ℤ → Submodule K A) (hF : ⨅ d, F d = ⊥)
    (x : A) (hx : ∀ d : ℤ, x ∈ F d) : x = 0 := by
  have hx' : x ∈ ⨅ d, F d := (Submodule.mem_iInf F).mpr hx
  rw [hF] at hx'
  exact hx'

/-- The source's exhaustive separated filtration has a nonzero initial form for
every nonzero element, as a genuine quotient-module element. -/
theorem exists_nonzero_initial_form (F : ℤ → Submodule K A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d) (hF : ⨅ d, F d = ⊥)
    {x : A} (hx : x ≠ 0) :
    ∃ (d : ℤ) (hd : x ∈ F d),
      (Submodule.Quotient.mk ⟨x, hd⟩ :
        (F d) ⧸ (F (d - 1)).comap (F d).subtype) ≠ 0 := by
  obtain ⟨d, hd, hprev⟩ := exists_initial_index
    (fun d => (F d : Set A)) (fun _ _ hij => hmono hij)
    hexhaustive (separated_of_iInf_eq_bot F hF) hx
  exact ⟨d, hd, initial_form_ne_zero F hd hprev⟩

end InitialForm

end IntegerFiltration
end StableCoordinate

end OAI
