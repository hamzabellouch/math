import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis
import OAI.Computability.UniqueGames.Gadgets.AdaptivePathsLemmas
import OAI.Computability.UniqueGames.Quadratic.Alignment
import OAI.Computability.UniqueGames.Quadratic.BlockSpanLemmas

namespace OAI

section

/-!
# Polynomial obstructions to collapsed or proportional binary inputs

One linear polynomial detects each nonzero input. One quadratic polynomial
detects each pair of distinct nonzero binary inputs. The witnesses are proved
nonzero by explicit coordinate-selector evaluations. Together with the
alignment obstruction they yield a finite product whose zero set contains
every failure of genericity. An `O_r(1/q)` bound suffices here.
-/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial

theorem exists_binary_coordinate_one {J : Type*} (t : J → ZMod 2) (ht : t ≠ 0) :
    ∃ j, t j = 1 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ht
  exact ⟨j, (binary_eq_zero_or_one (t j)).resolve_left hj⟩

/-- Distinct nonzero vectors over the binary field have a nonzero two-column
minor. Since the coefficient field is binary, the minor equals one. -/
theorem exists_binary_minor_one {J : Type*} (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    ∃ j k, t j * u k + t k * u j = 1 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  by_cases huj : u j = 0
  · obtain ⟨k, hk⟩ := exists_binary_coordinate_one u hu
    exact ⟨j, k, by simp [hj, huj, hk]⟩
  · have huj' : u j = 1 := (binary_eq_zero_or_one (u j)).resolve_left huj
    obtain ⟨k, hk⟩ := Function.ne_iff.mp htu
    refine ⟨j, k, ?_⟩
    rcases binary_eq_zero_or_one (t k) with htk | htk <;>
      rcases binary_eq_zero_or_one (u k) with huk | huk
    · exact (hk (htk.trans huk.symm)).elim
    · simp [hj, huj', htk, huk]
    · simp [hj, huj', htk, huk]
    · exact (hk (htk.trans huk.symm)).elim

section Polynomial

variable {J : Type*} [Fintype J]

/-- Set the first two rows of the indeterminate matrix to coordinate
selectors. The third row is zero. -/
noncomputable def selectorAssignment (j k : J) : (Fin 3 × J) → ZMod 2 := by
  classical
  exact fun x => if x.1 = 0 then (if x.2 = j then 1 else 0)
    else if x.1 = 1 then (if x.2 = k then 1 else 0) else 0

theorem eval_universalLinearForm_selector_zero (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 0) = t j := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem eval_universalLinearForm_selector_one (t : J → ZMod 2) (j k : J) :
    eval (selectorAssignment j k) (universalLinearForm t 1) = t k := by
  classical
  simp [universalLinearForm, selectorAssignment]

theorem universalLinearForm_zero_ne_zero (t : J → ZMod 2) (ht : t ≠ 0) :
    universalLinearForm t 0 ≠ 0 := by
  obtain ⟨j, hj⟩ := exists_binary_coordinate_one t ht
  intro h
  have hc := congrArg (eval (selectorAssignment j j)) h
  rw [eval_universalLinearForm_selector_zero, map_zero, hj] at hc
  exact one_ne_zero hc

/-- A two-row determinant, with subtraction equal to addition in
characteristic two. -/
noncomputable def universalPairMinor (t u : J → ZMod 2) :
    MvPolynomial (Fin 3 × J) (ZMod 2) :=
  universalLinearForm t 0 * universalLinearForm u 1 +
    universalLinearForm t 1 * universalLinearForm u 0

theorem universalPairMinor_ne_zero (t u : J → ZMod 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htu : t ≠ u) :
    universalPairMinor t u ≠ 0 := by
  obtain ⟨j, k, hjk⟩ := exists_binary_minor_one t u ht hu htu
  intro h
  have hc := congrArg (eval (selectorAssignment j k)) h
  simp only [universalPairMinor, map_add, map_mul,
    eval_universalLinearForm_selector_zero, eval_universalLinearForm_selector_one,
    map_zero] at hc
  rw [hjk] at hc
  exact one_ne_zero hc

/-- Proportional specialized image vectors force the fixed pair minor to
vanish, for every value of the proportionality scalar. -/
theorem universalPairMinor_eq_zero_of_proportional
    {F : Type*} [Field F] [CharP F 2]
    (t u : J → ZMod 2)
    (ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F) (a : F)
    (h : ∀ i, ρ (universalLinearForm t i) = a * ρ (universalLinearForm u i)) :
    ρ (universalPairMinor t u) = 0 := by
  simp only [universalPairMinor, map_add, map_mul, h]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (CharTwo.add_self_eq_zero
      (a * ρ (universalLinearForm u 0) * ρ (universalLinearForm u 1)))

end Polynomial

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Finite-field polynomial exceptional events

The nonzero polynomial obstruction for each fixed input set gives a uniform
bound over all linear lifts.  Its coefficients lie in the binary prime field,
so its degree is fixed before the extension field is chosen.  The theorems
below keep this order explicit and combine finitely many obstructions without
any union over maps.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

/-- The exact uniform probability on an explicit finite assignment space. -/
def assignmentProbability {n : ℕ} (event : (Fin n → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n

omit [Field F] in
theorem assignmentProbability_mono {n : ℕ}
    {event event' : (Fin n → F) → Prop} (h : ∀ x, event x → event' x) :
    assignmentProbability event ≤ assignmentProbability event' := by
  classical
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Finset.card_le_card
    (show Finset.univ.filter event ⊆ Finset.univ.filter event' from by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

/-- The checked Schwartz-Zippel theorem on the whole finite field. -/
theorem assignmentProbability_eval_zero_le {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  simpa [assignmentProbability] using
    MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)

omit [Fintype F] in
/-- Injective coefficient extension preserves the total degree exactly. -/
theorem totalDegree_map_eq_of_injective {σ : Type*}
    (φ : K →+* F) (hφ : Function.Injective φ) (p : MvPolynomial σ K) :
    (MvPolynomial.map φ p).totalDegree = p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective p hφ]

/-- A prime-field polynomial gives the same fixed numerator in every finite
extension field.  Only the denominator grows with the field size. -/
theorem assignmentProbability_eval₂_zero_le {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  have hp' : MvPolynomial.map φ p ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.map_injective φ hφ
    simpa using hz
  have h := assignmentProbability_eval_zero_le (MvPolynomial.map φ p) hp'
  simpa only [← MvPolynomial.eval₂_eq_eval_map,
    totalDegree_map_eq_of_injective φ hφ] using h

/-- An exceptional event contained in a polynomial zero set satisfies the
same bound, including events expressed by existence of an arbitrary lift. -/
theorem assignmentProbability_le_of_polynomial {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (event : (Fin n → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    assignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F :=
  (assignmentProbability_mono hvanish).trans
    (assignmentProbability_eval₂_zero_le φ hφ p hp)

/-- A fixed finite family of exceptional events admits a single fixed-degree
bound.  There is still no enumeration or union over the possible lifts. -/
theorem assignmentProbability_union_le {n : ℕ} {J : Type*} [Fintype J]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : J → MvPolynomial (Fin n) K) (hp : ∀ j, p j ≠ 0)
    (event : J → (Fin n → F) → Prop)
    (hvanish : ∀ j x, event j x → MvPolynomial.eval₂ φ x (p j) = 0) :
    assignmentProbability (fun x => ∃ j, event j x) ≤
      ((∑ j, (p j).totalDegree : ℕ) : ℚ≥0) / Fintype.card F := by
  classical
  let P : MvPolynomial (Fin n) K := ∏ j, p j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  have hvanishP : ∀ x, (∃ j, event j x) → MvPolynomial.eval₂ φ x P = 0 := by
    intro x hx
    obtain ⟨j, hj⟩ := hx
    change (MvPolynomial.eval₂Hom φ x) P = 0
    simp only [P, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hvanish j x hj)
  have hbound := assignmentProbability_le_of_polynomial φ hφ P hP _ hvanishP
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast MvPolynomial.totalDegree_finsetProd Finset.univ p

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Polynomial exceptional events on arbitrary finite variable sets

Reindexing the variable set transports both the polynomial and the uniform
assignment space. Thus the checked finite-field zero bound applies directly
to the three-by-r variables in the genericity proof, without changing the
degree or taking a union over possible linear lifts.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

/-- Reindexing an assignment transports it contravariantly along the variable
equivalence. -/
def reindexAssignments (e : σ ≃ τ) : (σ → F) ≃ (τ → F) where
  toFun x := fun t => x (e.symm t)
  invFun y := fun s => y (e s)
  left_inv x := by funext s; simp
  right_inv y := by funext t; simp

/-- Uniform assignment probability for an arbitrary finite variable set. -/
def finiteAssignmentProbability [Fintype σ] (event : (σ → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) /
    (Fintype.card F : ℚ≥0) ^ Fintype.card σ

omit [Field F] in
theorem finiteAssignmentProbability_reindex [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (event : (σ → F) → Prop) :
    finiteAssignmentProbability event =
      assignmentProbability (fun y : Fin n → F => event (fun s => y (e s))) := by
  classical
  have hcard : Fintype.card σ = n := by simpa using Fintype.card_congr e
  have hevent (x : σ → F) :
      event x ↔ event (fun s => reindexAssignments e x (e s)) := by
    simp [reindexAssignments]
  have hsub := Fintype.card_congr ((reindexAssignments (F := F) e).subtypeEquiv
    (p := event) (q := fun y : Fin n → F => event (fun s => y (e s))) hevent)
  have hfilter : (Finset.univ.filter event).card =
      (Finset.univ.filter (fun y : Fin n → F => event (fun s => y (e s)))).card := by
    simpa only [Fintype.card_subtype] using hsub
  simp only [finiteAssignmentProbability, assignmentProbability, hfilter, hcard]

/-- A bad event contained in a fixed nonzero polynomial's zero set has
probability at most its total degree divided by the field size. -/
theorem finiteAssignmentProbability_le_of_polynomial [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0)
    (event : (σ → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    finiteAssignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' := MvPolynomial.renameEquiv K e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e event]
  have hbound := assignmentProbability_le_of_polynomial φ hφ p' hp'
    (fun y => event (fun s => y (e s))) (by
      intro y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e p) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

theorem finiteAssignmentProbability_eval₂_zero_le [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0) :
    finiteAssignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F :=
  finiteAssignmentProbability_le_of_polynomial φ hφ p hp _ (fun _ h => h)

/-- A finite family of input-set obstructions yields a fixed total numerator.
The family index is independent of the chosen linear lift. -/
theorem finiteAssignmentProbability_union_le [Fintype σ] {J : Type*} [Fintype J]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : J → MvPolynomial σ K) (hp : ∀ j, p j ≠ 0)
    (event : J → (σ → F) → Prop)
    (hvanish : ∀ j x, event j x → MvPolynomial.eval₂ φ x (p j) = 0) :
    finiteAssignmentProbability (fun x => ∃ j, event j x) ≤
      ((∑ j, (p j).totalDegree : ℕ) : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' : J → MvPolynomial (Fin (Fintype.card σ)) K :=
    fun j => MvPolynomial.renameEquiv K e (p j)
  have hp' (j : J) : p' j ≠ 0 := by
    intro h
    apply hp j
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e]
  have hbound := assignmentProbability_union_le φ hφ p' hp'
    (fun j y => event j (fun s => y (e s))) (by
      intro j y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e (p j)) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish j (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Rank-loss accounting for quadratic blocks

A nonzero kernel character determines the field line of a lossy block.  On
a generic space there is at most one such character on each field line, so
the rank drops by at most one.  Counting the possible determining characters
also bounds the number of lossy lines.  These are deterministic statements;
the random orientation may be selected only after this data is fixed.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {R V W I : Type*} [Field R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup W] [Module R W]

/-- A vector space with at most one nonzero vector has dimension at most one.
The statement is deliberately independent of any characteristic assumption. -/
theorem finrank_le_one_of_nonzero_unique
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → v = w) :
    Module.finrank R V ≤ 1 := by
  classical
  by_cases hex : ∃ v : V, v ≠ 0
  · obtain ⟨v, hv⟩ := hex
    apply finrank_le_one v
    intro w
    by_cases hw : w = 0
    · exact ⟨0, by simp [hw]⟩
    · exact ⟨1, by simpa using h v w hv hw⟩
  · apply finrank_le_one (0 : V)
    intro w
    have hw : w = 0 := by
      by_contra hw
      exact hex ⟨w, hw⟩
    exact ⟨0, by simp [hw]⟩

/-- Nonproportionality of a generic character space makes every child kernel
at most one-dimensional once the field-line kernel criterion is applied. -/
theorem finrank_ker_le_one_of_nonzero_unique (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R f.ker ≤ 1 := by
  apply finrank_le_one_of_nonzero_unique
  intro v w hv hw
  apply Subtype.ext
  apply h v w
  · intro hv0
    apply hv
    exact Subtype.ext hv0
  · intro hw0
    apply hw
    exact Subtype.ext hw0
  · exact v.property
  · exact w.property

/-- Consequently the image rank can lose at most one dimension. -/
theorem finrank_source_le_range_add_one [FiniteDimensional R V]
    (f : V →ₗ[R] W)
    (h : ∀ v w : V, v ≠ 0 → w ≠ 0 → f v = 0 → f w = 0 → v = w) :
    Module.finrank R V ≤ Module.finrank R f.range + 1 := by
  have hk := finrank_ker_le_one_of_nonzero_unique f h
  have hr := f.finrank_range_add_finrank_ker
  omega

variable [Fintype V] [Fintype I] [DecidableEq I]

/-- The actual finite event of a child map having a nonzero kernel. -/
def lossIndices (f : I → V →ₗ[R] W) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => ∃ v : V, v ≠ 0 ∧ f i v = 0)

def alignedCharacters (aligned : V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ aligned v)

theorem lossIndices_subset_image (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    lossIndices f ⊆ (alignedCharacters aligned).image lineOf := by
  classical
  intro i hi
  obtain ⟨v, hv, hfv⟩ := (Finset.mem_filter.mp hi).2
  obtain ⟨halign, hline⟩ := hkernel i v hv hfv
  apply Finset.mem_image.mpr
  exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, halign⟩, hline⟩

/-- The cardinality bound does not union over lifts or orientations. -/
theorem card_lossIndices_le_card_aligned (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i) :
    (lossIndices f).card ≤ (alignedCharacters aligned).card := by
  classical
  exact (Finset.card_le_card (lossIndices_subset_image f aligned lineOf hkernel)).trans
    (Finset.card_image_le (s := alignedCharacters aligned) (f := lineOf))

theorem card_lossIndices_le (f : I → V →ₗ[R] W)
    (aligned : V → Prop) (lineOf : V → I) (r : ℕ)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → aligned v ∧ lineOf v = i)
    (hgeneric : (alignedCharacters aligned).card ≤ 3 * r) :
    (lossIndices f).card ≤ 3 * r :=
  (card_lossIndices_le_card_aligned f aligned lineOf hkernel).trans hgeneric

theorem card_lossIndices_le_nonzero (f : I → V →ₗ[R] W)
    (lineOf : V → I)
    (hkernel : ∀ i v, v ≠ 0 → f i v = 0 → lineOf v = i) :
    (lossIndices f).card ≤ Fintype.card V - 1 := by
  classical
  have h := card_lossIndices_le_card_aligned f (fun _ => True) lineOf
    (fun i v hv hfv => ⟨trivial, hkernel i v hv hfv⟩)
  simpa [alignedCharacters, Finset.filter_ne'] using h

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem squareMap_injective : Function.Injective (fun x : F => x ^ 2) := by
  intro x y h
  change x ^ 2 = y ^ 2 at h
  have hs : (x + y) ^ 2 = 0 := by
    rw [CharTwo.add_sq, h, CharTwo.add_self_eq_zero]
  have hz : x + y = 0 := (sq_eq_zero_iff).mp hs
  exact (add_eq_zero_iff_eq_neg.mp hz).trans (CharTwo.neg_eq y)

/-- The unique square root, obtained by bijectivity of the finite square map. -/
noncomputable def squareRoot (c : F) : F :=
  Classical.choose (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_sq (c : F) : squareRoot c ^ 2 = c :=
  Classical.choose_spec (Finite.surjective_of_injective squareMap_injective c)

@[simp] theorem squareRoot_of_sq (c : F) : squareRoot (c ^ 2) = c := by
  apply squareMap_injective
  exact squareRoot_sq _

theorem squareRoot_unique {c r : F} (h : r ^ 2 = c) : r = squareRoot c := by
  apply squareMap_injective
  change r ^ 2 = squareRoot c ^ 2
  rw [h, squareRoot_sq]

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators

noncomputable section

section AlignmentEvents

variable {R F V ι n : Type*}
variable [Field R] [Field F] [Algebra R F]
variable [AddCommGroup V] [Module R V]
variable [Fintype V] [Fintype ι] [Fintype n]

/-- Nonzero inputs aligned by a specified linear lift. -/
def alignmentEvent (z : V → n → F) (g : V →ₗ[R] (n → F)) (c : V → F) :
    Finset V := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ (∑ i, z v i * g v i) = c v)

/-- Exact finite bad-set reduction.  Its right hand side quantifies only over
input sets, while column membership already accounts for every linear lift. -/
theorem all_lifts_bound_iff_subsets (b : Basis ι R V) (z : V → n → F)
    (c : V → F) (k : ℕ) :
    (∀ g : V →ₗ[R] (n → F), (alignmentEvent z g c).card ≤ k) ↔
      ∀ E : Finset V, 0 ∉ E → E.card = k + 1 →
        (fun e : E => c e) ∉
          LinearMap.range (alignmentMatrix b (fun e : E => (e : V)) z).mulVecLin := by
  classical
  constructor
  · intro h E hzero hcard hmem
    obtain ⟨g, hg⟩ := (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mpr hmem
    have hsubset : E ⊆ alignmentEvent z g c := by
      intro v hv
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hg ⟨v, hv⟩⟩
      intro hvzero
      exact hzero (hvzero ▸ hv)
    have hle := (Finset.card_le_card hsubset).trans (h g)
    omega
  · intro h g
    by_contra hbad
    have hlarge : k + 1 ≤ (alignmentEvent z g c).card := by omega
    obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
    have hzero : (0 : V) ∉ E := by
      intro hz
      have hh := (Finset.mem_filter.mp (hsub hz)).2.1
      exact hh rfl
    apply h E hzero hcard
    apply (exists_lift_alignment_iff_mem_range b
      (fun e : E => (e : V)) z (fun e : E => c e)).mp
    refine ⟨g, ?_⟩
    intro e
    exact (Finset.mem_filter.mp (hsub e.property)).2.2

theorem all_lifts_bound_of_card_le (z : V → n → F) (c : V → F) (k : ℕ)
    (hcard : Fintype.card V - 1 ≤ k) (g : V →ₗ[R] (n → F)) :
    (alignmentEvent z g c).card ≤ k := by
  classical
  have hsub : alignmentEvent z g c ⊆ Finset.univ.erase (0 : V) := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hv).2.1, Finset.mem_univ _⟩
  have hle := Finset.card_le_card hsub
  simpa using hle.trans (by simpa using hcard)

end AlignmentEvents

section BinaryGenericity

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The cubic square-root right hand side of the alignment equation. -/
def alignmentRightHandSide (z : Fin 3 → F) : F := squareRoot (z 0 * z 1 * z 2)

/-- The complete genericity predicate. The universal linear
map quantifier occurs inside the property of the selected subspace. -/
def IsGeneric (S : Submodule (ZMod 2) (Fin 3 → F)) : Prop := by
  classical
  exact
    (∀ z w : S, z ≠ 0 → w ≠ 0 →
      (∃ t : F, (z : Fin 3 → F) = t • (w : Fin 3 → F)) → z = w) ∧
    (∀ g : S →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent (R := ZMod 2) (fun z : S => (z : Fin 3 → F)) g
        (fun z : S => alignmentRightHandSide (z : Fin 3 → F))).card ≤
          3 * Module.finrank (ZMod 2) S)

end BinaryGenericity

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# Passing genericity from a parametrization to its actual image

An injective binary-linear parametrization identifies its domain with the
image subspace. The universal quantifier over linear lifts is transported
by composition, and alignment-event cardinalities agree exactly.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

variable {F V : Type*} [Field F] [Fintype F] [CharP F 2]
variable [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- The actual range of an injective parametrization is generic when its
nonproportionality and all-lifts alignment bounds hold on the domain. -/
theorem isGeneric_range_of_injective
    (z : V →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z)
    (hseparate : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      (∃ t : F, z v = t • z w) → v = w)
    (halign : ∀ g : V →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent z g (fun v => alignmentRightHandSide (z v))).card ≤
        3 * Module.finrank (ZMod 2) V) :
    IsGeneric (LinearMap.range z) := by
  classical
  let : Fintype (LinearMap.range z) := Subtype.fintype (Membership.mem (LinearMap.range z))
  let e : V ≃ₗ[ZMod 2] LinearMap.range z := LinearEquiv.ofInjective z hz
  have he (v : V) : ((e v : LinearMap.range z) : Fin 3 → F) = z v := rfl
  have hes (s : LinearMap.range z) : z (e.symm s) = (s : Fin 3 → F) :=
    LinearEquiv.ofInjective_symm_apply z s
  have hzero (v : V) : e v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, map_zero]
    · intro h hv
      apply h
      apply e.injective
      simpa only [map_zero] using hv
  constructor
  · intro s t hs ht hprop
    have hs' : e.symm s ≠ 0 := by
      intro h
      apply hs
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have ht' : e.symm t ≠ 0 := by
      intro h
      apply ht
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have hinput : e.symm s = e.symm t := by
      apply hseparate _ _ hs' ht'
      simpa only [hes] using hprop
    exact e.symm.injective hinput
  · intro g
    have hevent (v : V) :
        v ∈ alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v)) ↔
        e v ∈ alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F)) := by
      simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        LinearMap.comp_apply, LinearEquiv.coe_coe, he, hzero]
    have hcard :
        (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card =
        (alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F))).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        exact (hevent v).mp hv
      · intro v hv w hw h
        exact e.injective h
      · intro s hs
        refine ⟨e.symm s, (hevent (e.symm s)).mpr ?_, e.apply_symm_apply s⟩
        simpa only [e.apply_symm_apply] using hs
    calc
      _ = (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card := hcard.symm
      _ ≤ 3 * Module.finrank (ZMod 2) V := halign _
      _ = 3 * Module.finrank (ZMod 2) (LinearMap.range z) :=
        congrArg (fun d : ℕ => 3 * d) e.finrank_eq

omit [Fintype F] [CharP F 2] in
/-- In the basis-parametrized case, the image rank is the number of binary
input coordinates. -/
theorem finrank_range_binary_parameters {J : Type*} [Fintype J]
    (z : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z) :
    Module.finrank (ZMod 2) (LinearMap.range z) = Fintype.card J := by
  rw [LinearMap.finrank_range_of_inj hz, Module.finrank_fintype_fun_eq_card]

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# The finite nongeneric fraction

This definition records the actual uniform event on the rank-indexed
Grassmannian.
-/

noncomputable section

open UniqueGamesTheorem.Gadget.Orientation

namespace UniqueGamesTheorem.Quadratic

/-- The actual uniform fraction of nongeneric rank-`r` binary subspaces. -/
def nongenericFraction (F : Type*) [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] (r : ℕ) : ℚ :=
  (Nat.card {S : RankSpace (ZMod 2) (Fin 3 → F) r // ¬IsGeneric S.1} : ℚ) /
    Nat.card (RankSpace (ZMod 2) (Fin 3 → F) r)

end UniqueGamesTheorem.Quadratic

end

end

section

/-! The actual random binary-linear parametrization used in the genericity proof. -/

namespace UniqueGamesTheorem.Quadratic

open Module
open scoped BigOperators

noncomputable section

variable {F J : Type*} [Field F] [Algebra (ZMod 2) F] [Fintype J]

/-- Independent field entries specify a binary-linear map into `F³`. -/
def parameterMap (x : (Fin 3 × J) → F) : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) :=
  (Pi.basisFun (ZMod 2) J).constr (ZMod 2) (fun j i => x (i, j))

theorem parameterMap_apply (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    parameterMap x t i = ∑ j, algebraMap (ZMod 2) F (t j) * x (i, j) := by
  classical
  simp [parameterMap, Basis.constr_apply_fintype, Algebra.smul_def]

theorem parameterMap_basis (x : (Fin 3 × J) → F) (j : J) (i : Fin 3) :
    parameterMap x ((Pi.basisFun (ZMod 2) J) j) i = x (i, j) := by
  exact congrFun ((Pi.basisFun (ZMod 2) J).constr_basis (ZMod 2)
    (fun j i => x (i, j)) j) i

/-- Evaluation of the universal polynomial is the actual linear map. -/
theorem eval_universalLinearForm (x : (Fin 3 × J) → F) (t : J → ZMod 2) (i : Fin 3) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      parameterMap x t i := by
  rw [parameterMap_apply]
  simp [universalLinearForm]

/-- All linear lifts have the prescribed universal alignment columns, with
their arbitrary values on the binary basis as column coefficients. -/
theorem dot_parameter_lift (x : (Fin 3 × J) → F)
    (g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (t : J → ZMod 2) :
    (∑ i, parameterMap x t i * g t i) =
      ∑ ij : Fin 3 × J,
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
          (universalAlignmentColumn (fun t : J → ZMod 2 => t) ij t) *
          g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1 := by
  have h := dot_lift_eq_alignment_mulVec (Pi.basisFun (ZMod 2) J)
    (fun t : J → ZMod 2 => t) (parameterMap x) g t
  simpa [Matrix.mulVec, dotProduct, alignmentMatrix, Pi.basisFun_repr,
    universalAlignmentColumn, eval_universalLinearForm] using h

variable [Fintype F] [CharP F 2]

/-- The unique square-root value satisfies the universal cubic equation. -/
theorem alignmentRightHandSide_sq (x : (Fin 3 × J) → F) (t : J → ZMod 2) :
    alignmentRightHandSide (parameterMap x t) ^ 2 =
      MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x
        (∏ i : Fin 3, universalLinearForm t i) := by
  simp [alignmentRightHandSide, Fin.prod_univ_succ, eval_universalLinearForm, mul_assoc]

end

end UniqueGamesTheorem.Quadratic

end

end OAI
