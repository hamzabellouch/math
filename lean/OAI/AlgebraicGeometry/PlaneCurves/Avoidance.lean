import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import OAI.AlgebraicGeometry.PlaneCurves.Forms

namespace OAI

/-!
# Countable exceptional closed unions and simultaneous configuration avoidance
-/

section

/-!
The set-theoretic and countability portion of manuscript Lemma `lem:universal`.
The family `A` is arbitrary: the theorems do not assert incidence closedness,
properness, or the existence of a tuple avoiding the exceptional union.
-/
namespace Nagata.Workers.W25

/-- Every positive degree and every nonnegative multiplicity vector, without bounds. -/
abbrev IncidenceIndex (r : ℕ) := {d : ℕ // 0 < d} × (Fin r → ℕ)

instance incidenceIndex_countable (r : ℕ) : Countable (IncidenceIndex r) := by
  infer_instance

/-- Union of exactly the members of `A` which are proper subsets of the ambient type. -/
def exceptionalUnion {ι X : Type*} (A : ι → Set X) : Set X :=
  {x | ∃ i, A i ≠ Set.univ ∧ x ∈ A i}

/-- The family occurring in the union is countable when its index type is countable. -/
theorem properFamily_countable {ι X : Type*} [Countable ι] (A : ι → Set X) :
    {S : Set X | ∃ i, A i ≠ Set.univ ∧ S = A i}.Countable := by
  apply (Set.countable_range A).mono
  rintro S ⟨i, _, rfl⟩
  exact ⟨i, rfl⟩

/-- Avoiding this one union makes every supported incidence condition universal. -/
theorem member_eq_univ_of_avoids {ι X : Type*} (A : ι → Set X) {x : X}
    (hx : x ∉ exceptionalUnion A) {i : ι} (hi : x ∈ A i) : A i = Set.univ := by
  by_contra h
  exact hx ⟨i, h, hi⟩

/-- An explicit simultaneous quantifier: the same avoiding tuple works for all indices. -/
theorem avoids_iff_supported_universal {ι X : Type*} (A : ι → Set X) (x : X) :
    x ∉ exceptionalUnion A ↔ ∀ i, x ∈ A i → A i = Set.univ := by
  constructor
  · intro hx i hi
    exact member_eq_univ_of_avoids A hx hi
  · rintro hx ⟨i, hi, hxi⟩
    exact hi (hx i hxi)

/-- Conditional reduction, with the needed exclusion of bad universal loci explicit. -/
theorem simultaneous_exclusion {ι X : Type*} (A : ι → Set X) (bad : ι → Prop)
    (hproper : ∀ i, bad i → A i ≠ Set.univ) {x : X}
    (hx : x ∉ exceptionalUnion A) : ∀ i, bad i → x ∉ A i := by
  intro i hi hxi
  exact hproper i hi (member_eq_univ_of_avoids A hx hxi)

/-- Enumerate the proper loci as a natural-number sequence, padding with the empty
set. This also covers the case where there are no proper members. -/
theorem exists_exceptional_sequence {ι X : Type*} [Countable ι] (A : ι → Set X) :
    ∃ E : ℕ → Set X,
      (∀ n, E n = ∅ ∨ ∃ i, A i ≠ Set.univ ∧ E n = A i) ∧
      (∀ x, (∃ n, x ∈ E n) ↔ x ∈ exceptionalUnion A) := by
  classical
  let B : Set (Set X) := insert ∅ {S | ∃ i, A i ≠ Set.univ ∧ S = A i}
  have hB : B.Countable := (properFamily_countable A).insert ∅
  obtain ⟨E, hE⟩ := hB.exists_eq_range ⟨∅, Set.mem_insert _ _⟩
  have hEmem : ∀ n, E n ∈ B := by
    intro n
    rw [hE]
    exact ⟨n, rfl⟩
  refine ⟨E, fun n => hEmem n, ?_⟩
  intro x
  constructor
  · rintro ⟨n, hxn⟩
    rcases hEmem n with hempty | ⟨i, hi, heq⟩
    · rw [hempty] at hxn
      exact False.elim hxn
    · exact ⟨i, hi, heq ▸ hxn⟩
  · rintro ⟨i, hi, hxi⟩
    have hAi : A i ∈ B := Or.inr ⟨i, hi, rfl⟩
    rw [hE] at hAi
    obtain ⟨n, hn⟩ := hAi
    exact ⟨n, hn.symm ▸ hxi⟩

end Nagata.Workers.W25

end

section

/-! Nonempty simultaneous avoidance of any countable family of proper relative
Zariski closed subsets of the actual ordered configuration space. -/
noncomputable section
namespace Nagata.Workers.W25
open Nagata.ProjectiveGeometry

/-- A proper relative closed locus has a nonzero multihomogeneous equation
vanishing at every point of that locus. -/
theorem exists_nonzero_equation_of_proper_closed {r : ℕ}
    (S : Set (OrderedDistinctPoints r)) (hclosed : IsConfigurationZariskiClosed S)
    (hproper : S ≠ Set.univ) :
    ∃ F : MultihomogeneousEquation r, F.polynomial ≠ 0 ∧
      ∀ P ∈ S, equationVanishes F P.val := by
  classical
  obtain ⟨T, ⟨E, hE⟩, hST⟩ := hclosed
  have hex : ∃ P : OrderedDistinctPoints r, P ∉ S := by
    by_contra h
    apply hproper
    ext P
    simp only [Set.mem_univ, iff_true]
    by_contra hp
    exact h ⟨P, hp⟩
  obtain ⟨P, hP⟩ := hex
  have hnot : ¬ ∀ F ∈ E, equationVanishes F P.val := by
    intro h
    exact hP ((hST P).mpr ((hE P.val).mpr h))
  push Not at hnot
  obtain ⟨F, hFE, hF⟩ := hnot
  refine ⟨F, ?_, fun Q hQ => (hE Q.val).mp ((hST Q).mp hQ) F hFE⟩
  intro hzero
  apply hF
  intro v hv hrep
  simp [hzero]

/-- Every countable family of proper relative Zariski closed subsets of the
space of ordered distinct complex projective plane points has a common avoiding point. -/
theorem exists_configuration_avoiding_closed_family {r : ℕ} {ι : Type*} [Countable ι]
    (S : ι → Set (OrderedDistinctPoints r))
    (hclosed : ∀ i, IsConfigurationZariskiClosed (S i))
    (hproper : ∀ i, S i ≠ Set.univ) :
    ∃ P : OrderedDistinctPoints r, ∀ i, P ∉ S i := by
  classical
  choose F hFne hFvan using
    fun i => exists_nonzero_equation_of_proper_closed (S i) (hclosed i) (hproper i)
  obtain ⟨x, P, hP, hx⟩ := exists_projective_affine_avoidance
    (fun i => Nagata.W16.blockDehomogenize (F i))
    (fun i => Nagata.W16.blockDehomogenize_ne_zero (F i) (hFne i))
  refine ⟨P, fun i hPS => ?_⟩
  apply hx i
  rw [Nagata.W16.eval_blockDehomogenize]
  exact hFvan i P hPS
    (fun k => affinePlaneVector (fun j => x (k, j)))
    (fun k => affinePlaneVector_ne_zero (fun j => x (k, j)))
    (fun k => (hP k).symm)

/-- The specific exceptional union of proper members of a closed incidence family
has nonempty complement; it is one union for all indices simultaneously. -/
theorem exists_outside_exceptionalUnion {r : ℕ} {ι : Type*} [Countable ι]
    (A : ι → Set (OrderedDistinctPoints r))
    (hclosed : ∀ i, IsConfigurationZariskiClosed (A i)) :
    ∃ P : OrderedDistinctPoints r, P ∉ exceptionalUnion A := by
  obtain ⟨P, hP⟩ := exists_configuration_avoiding_closed_family
    (fun i : {i // A i ≠ Set.univ} => A i.val)
    (fun i => hclosed i.val) (fun i => i.property)
  refine ⟨P, ?_⟩
  rintro ⟨i, hi, hPi⟩
  exact hP ⟨i, hi⟩ hPi

/-- Natural-number exceptional sequence matching the full target's quantifier shape.
Its complement is nonempty and exactly the complement of the proper-locus union. -/
theorem exists_closed_exceptional_sequence {r : ℕ} {ι : Type*} [Countable ι]
    (A : ι → Set (OrderedDistinctPoints r))
    (hclosed : ∀ i, IsConfigurationZariskiClosed (A i)) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ P, ∀ n, P ∉ E n) ∧
      (∀ P, (∀ n, P ∉ E n) ↔ P ∉ exceptionalUnion A) := by
  obtain ⟨E, hEn, hcover⟩ := exists_exceptional_sequence A
  have havoid : ∀ P, (∀ n, P ∉ E n) ↔ P ∉ exceptionalUnion A := by
    intro P
    constructor
    · intro hP hPe
      obtain ⟨n, hn⟩ := (hcover P).mpr hPe
      exact hP n hn
    · intro hP n hn
      exact hP ((hcover P).mp ⟨n, hn⟩)
  obtain ⟨P, hP⟩ := exists_outside_exceptionalUnion A hclosed
  refine ⟨E, ?_, ⟨P, (havoid P).mpr hP⟩, havoid⟩
  intro n
  rcases hEn n with hempty | ⟨i, hi, hEi⟩
  · rw [hempty]
    exact ⟨isConfigurationZariskiClosed_empty r, configuration_empty_ne_univ r⟩
  · rw [hEi]
    exact ⟨hclosed i, hi⟩

end Nagata.Workers.W25

end
end

end OAI
