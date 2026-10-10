import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Units.Equiv
import OAI.AlgebraicGeometry.PlaneCurves.ArithmeticReduction
import OAI.AlgebraicGeometry.PlaneCurves.Avoidance

namespace OAI

/-!
# Permutation, universal support, and simultaneous multiplicity reduction
-/

section

/-! Finite algebra in the permutation-product reduction of manuscript Lemma
`lem:universal`, section 01. These lemmas do not assert incidence closedness,
existence of forms, or the geometric additivity of multiplicity. -/
namespace Nagata.W13
open scoped BigOperators

/-- Permutation symmetrization gives the same multiplicity at every position. -/
theorem permutation_sum_independent {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i j : α) :
    (∑ σ : Equiv.Perm α, m (σ i)) = ∑ σ : Equiv.Perm α, m (σ j) := by
  apply Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i j))
  intro σ
  simp [Equiv.Perm.mul_apply]

/-- The double sum counts each permutation's total multiplicity once. -/
theorem card_mul_permutation_sum {α : Type*} [Fintype α] [DecidableEq α]
    (m : α → ℕ) (i : α) :
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
      (Fintype.card α).factorial * ∑ j, m j := by
  calc
    Fintype.card α * (∑ σ : Equiv.Perm α, m (σ i)) =
        ∑ j : α, ∑ σ : Equiv.Perm α, m (σ j) := by
      simp_rw [← permutation_sum_independent m i]
      simp
    _ = ∑ σ : Equiv.Perm α, ∑ j : α, m (σ j) := Finset.sum_comm
    _ = ∑ _σ : Equiv.Perm α, ∑ j : α, m j := by
      apply Finset.sum_congr rfl
      intro σ _
      exact Equiv.sum_comp σ m
    _ = (Fintype.card α).factorial * ∑ j, m j := by
      simp [Fintype.card_perm]

/-- Each original multiplicity occurs `(r-1)!` times at each position. -/
theorem permutation_sum_multiplicity {r : ℕ} (hr : 0 < r)
    (m : Fin r → ℕ) (i : Fin r) :
    (∑ σ : Equiv.Perm (Fin r), m (σ i)) =
      (r - 1).factorial * ∑ j, m j := by
  apply Nat.eq_of_mul_eq_mul_left hr
  have h := card_mul_permutation_sum m i
  simp only [Fintype.card_fin] at h
  have hfac := Nat.factorial_succ (r - 1)
  rw [Nat.sub_add_cancel hr] at hfac
  rw [h, ← Nat.mul_assoc, ← hfac]

/-- The product of the chosen nonzero forms remains nonzero in a domain. -/
theorem permutation_product_ne_zero {α R : Type*} [Fintype α] [DecidableEq α]
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (f : Equiv.Perm α → R) (hf : ∀ σ, f σ ≠ 0) :
    (∏ σ, f σ) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun σ _ => hf σ)

end Nagata.W13

end

section

/-!
# The permutation-product reduction for actual homogeneous equations
-/

noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- Every ordered distinct tuple supports a nonzero equation with the given
multiplicity vector. This is a definition of the intermediate universal system,
not an assumption about which such systems exist. -/
def UniversalSupport (r d : ℕ) (m : Fin r → ℕ) : Prop :=
  ∀ p : OrderedDistinctPoints r,
    ∃ F : MvPolynomial (Fin 3) ℂ,
      F ≠ 0 ∧ F.IsHomogeneous d ∧
      ∀ i, multiplicityAtLeast F (p.val i) (m i)

/-- Finite products add the chart ideal-power multiplicity lower bounds. -/
theorem multiplicityAtLeast_prod {ι : Type*} (s : Finset ι)
    (p : PlanePoint) (m : ι → ℕ) (F : ι → MvPolynomial (Fin 3) ℂ)
    (h : ∀ i ∈ s, multiplicityAtLeast (F i) p (m i)) :
    multiplicityAtLeast (∏ i ∈ s, F i) p (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using multiplicityAtLeast_zero (1 : MvPolynomial (Fin 3) ℂ) p
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      exact multiplicityAtLeast_mul (h a (Finset.mem_insert_self a s))
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Reordering a configuration reorders the prescribed multiplicities. -/
theorem universalSupport_permute {r d : ℕ} {m : Fin r → ℕ}
    (h : UniversalSupport r d m) (σ : Equiv.Perm (Fin r)) :
    UniversalSupport r d (fun i => m (σ i)) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h
    ⟨fun j => p.val (σ.symm j), p.property.comp σ.symm.injective⟩
  refine ⟨F, hne, hhom, ?_⟩
  intro i
  simpa using hm (σ i)

/-- Universal support of an arbitrary multiplicity vector gives universal
support of the constant vector `(r-1)! * sum m`, at degree `r! * d`.
This includes unequal and zero entries in `m` and all nonzero homogeneous forms,
including reducible and nonreduced equations. -/
theorem universalSupport_symmetrize {r d : ℕ} (hr : 0 < r)
    {m : Fin r → ℕ} (h : UniversalSupport r d m) :
    UniversalSupport r (r.factorial * d)
      (fun _ => (r - 1).factorial * ∑ i, m i) := by
  classical
  intro p
  have hs : ∀ σ : Equiv.Perm (Fin r),
      ∃ F : MvPolynomial (Fin 3) ℂ,
        F ≠ 0 ∧ F.IsHomogeneous d ∧
          ∀ i, multiplicityAtLeast F (p.val i) (m (σ i)) :=
    fun σ => universalSupport_permute h σ p
  let F := fun σ => Classical.choose (hs σ)
  have hne : ∀ σ, F σ ≠ 0 := fun σ => (Classical.choose_spec (hs σ)).1
  have hhom : ∀ σ, (F σ).IsHomogeneous d :=
    fun σ => (Classical.choose_spec (hs σ)).2.1
  have hm : ∀ σ i, multiplicityAtLeast (F σ) (p.val i) (m (σ i)) :=
    fun σ => (Classical.choose_spec (hs σ)).2.2
  have hp := W16.finite_product_forms Finset.univ F (fun _ => d)
    (fun σ _ => hhom σ) (fun σ _ => hne σ)
  refine ⟨∏ σ, F σ, hp.1, ?_, ?_⟩
  · simpa [Fintype.card_perm] using hp.2.1
  · intro i
    have hi := multiplicityAtLeast_prod Finset.univ (p.val i)
      (fun σ => m (σ i)) F (fun σ _ => hm σ i)
    rw [permutation_sum_multiplicity hr m i] at hi
    exact hi

/-- Raising each actual equation to a power scales its degree and every
multiplicity lower bound, so universal systems are closed under common multiples. -/
theorem universalSupport_pow {r d : ℕ} {m : Fin r → ℕ}
    (h : UniversalSupport r d m) (N : ℕ) :
    UniversalSupport r (d * N) (fun i => m i * N) := by
  intro p
  obtain ⟨F, hne, hhom, hm⟩ := h p
  exact ⟨F ^ N, pow_ne_zero N hne, hhom.pow N,
    fun i => multiplicityAtLeast_pow (hm i) N⟩

end Nagata.W13

end
end

section

noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- The actual homogeneous-polynomial incidence condition at a configuration. -/
def supportLocus (r : ℕ) (i : Workers.W25.IncidenceIndex r) :
    Set (OrderedDistinctPoints r) :=
  {p | ∃ F : MvPolynomial (Fin 3) ℂ,
    F ≠ 0 ∧ F.IsHomogeneous i.1.val ∧
      ∀ j, multiplicityAtLeast F (p.val j) (i.2 j)}

/-- One exceptional union indexed by all positive degrees and all nonnegative
multiplicity vectors, retaining exactly the proper support loci. -/
def supportExceptionalUnion (r : ℕ) : Set (OrderedDistinctPoints r) :=
  Workers.W25.exceptionalUnion (supportLocus r)

/-- The proper support loci form a countable family covering all positive
integer degrees and all nonnegative multiplicity vectors simultaneously. -/
theorem properSupportFamily_countable (r : ℕ) :
    {S : Set (OrderedDistinctPoints r) |
      ∃ i : Workers.W25.IncidenceIndex r,
        supportLocus r i ≠ Set.univ ∧ S = supportLocus r i}.Countable :=
  Workers.W25.properFamily_countable (supportLocus r)

/-- Outside the one exceptional union, every supported multiplicity system
is universal on the whole genuine configuration space. -/
theorem universalSupport_of_avoids {r d : ℕ} (hd : 0 < d)
    {m : Fin r → ℕ} {p : OrderedDistinctPoints r}
    (hp : p ∉ supportExceptionalUnion r)
    (hF : ∃ F : MvPolynomial (Fin 3) ℂ,
      F ≠ 0 ∧ F.IsHomogeneous d ∧
        ∀ i, multiplicityAtLeast F (p.val i) (m i)) :
    UniversalSupport r d m := by
  have hA : supportLocus r (⟨d, hd⟩, m) = Set.univ :=
    Workers.W25.member_eq_univ_of_avoids (supportLocus r) hp hF
  intro q
  have hq : q ∈ supportLocus r (⟨d, hd⟩, m) := by
    rw [hA]
    exact Set.mem_univ q
  exact hq

/-- A violating equation outside the single exceptional union produces
positive integers `D,M` with `D/M ≤ sqrt r` and universal equal-multiplicity
support. Topological closedness and nonemptiness of avoidance remain separate;
there is no assumption about normal bundles or interpolation in this reduction. -/
theorem universalEqualSupport_of_violation {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {m : Fin r → ℕ} {p : OrderedDistinctPoints r}
    (hp : p ∉ supportExceptionalUnion r)
    (hF : ∃ F : MvPolynomial (Fin 3) ℂ,
      F ≠ 0 ∧ F.IsHomogeneous d ∧
        ∀ i, multiplicityAtLeast F (p.val i) (m i))
    (hbad : (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ)) :
    ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ (D : ℝ) / M ≤ Real.sqrt r ∧
      UniversalSupport r D (fun _ => M) := by
  have hbad' : (d : ℝ) * Real.sqrt r ≤ (∑ i, m i : ℕ) := by
    simpa using hbad
  have harith := Workers.W14.factorial_symmetrization hr hd hbad'
  exact ⟨r.factorial * d, (r - 1).factorial * ∑ i, m i,
    harith.1, harith.2.1, harith.2.2,
    universalSupport_symmetrize hr (universalSupport_of_avoids hd hp hF)⟩

end Nagata.W13

end
end

section

/-!
# Universal reduction with one closed exceptional sequence
-/
noncomputable section
namespace Nagata.W13
open ProjectiveGeometry
open scoped BigOperators

/-- The source reduction, conditional only on projective closedness of actual
support loci. The same exceptional sequence handles every positive degree and
all nonnegative unequal multiplicity vectors simultaneously. -/
theorem source_universal_reduction_of_incidence_closed
    (r : ℕ) (hr : 10 ≤ r)
    (hclosed : ∀ i : Workers.W25.IncidenceIndex r,
      IsConfigurationZariskiClosed (supportLocus r i)) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (d : ℝ) * Real.sqrt r ≤ ∑ i, (m i : ℝ) →
          ∃ D M : ℕ, 0 < D ∧ 0 < M ∧ (D : ℝ) / M ≤ Real.sqrt r ∧
            UniversalSupport r D (fun _ => M) := by
  obtain ⟨E, hEclosed, hEnonempty, hEavoid⟩ :=
    Workers.W25.exists_closed_exceptional_sequence (supportLocus r) hclosed
  refine ⟨E, hEclosed, hEnonempty, ?_⟩
  intro p hp d hd F hFne hFhom m hmult hbad
  have hrpos : 0 < r := lt_of_lt_of_le (by decide : 0 < 10) hr
  exact universalEqualSupport_of_violation hrpos hd
    ((hEavoid p).mp hp) ⟨F, hFne, hFhom, hmult⟩ hbad

theorem strict_bound_of_incidence_closed_and_no_universal
    (r : ℕ) (hr : 10 ≤ r)
    (hclosed : ∀ i : Workers.W25.IncidenceIndex r,
      IsConfigurationZariskiClosed (supportLocus r i))
    (hno : ∀ D M : ℕ, 0 < D → 0 < M →
      (D : ℝ) / M ≤ Real.sqrt r → ¬ UniversalSupport r D (fun _ => M)) :
    ∃ E : ℕ → Set (OrderedDistinctPoints r),
      (∀ n, IsConfigurationZariskiClosed (E n) ∧ E n ≠ Set.univ) ∧
      (∃ p : OrderedDistinctPoints r, ∀ n, p ∉ E n) ∧
      ∀ p : OrderedDistinctPoints r, (∀ n, p ∉ E n) →
        ∀ (d : ℕ), 1 ≤ d →
        ∀ F : MvPolynomial (Fin 3) ℂ, F ≠ 0 → F.IsHomogeneous d →
        ∀ m : Fin r → ℕ,
          (∀ i, multiplicityAtLeast F (p.val i) (m i)) →
          (∑ i, (m i : ℝ)) < (d : ℝ) * Real.sqrt r := by
  obtain ⟨E, hEclosed, hEnonempty, hreduce⟩ :=
    source_universal_reduction_of_incidence_closed r hr hclosed
  refine ⟨E, hEclosed, hEnonempty, ?_⟩
  intro p hp d hd F hFne hFhom m hmult
  by_contra hlt
  obtain ⟨D, M, hD, hM, hslope, hU⟩ :=
    hreduce p hp d hd F hFne hFhom m hmult (le_of_not_gt hlt)
  exact hno D M hD hM hslope hU

end Nagata.W13

end
end

end OAI
