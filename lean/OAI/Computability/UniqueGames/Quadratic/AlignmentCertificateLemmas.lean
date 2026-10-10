import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Trace.Basic
import OAI.Computability.UniqueGames.Quadratic.BlockSpanLemmas
import OAI.Computability.UniqueGames.Quadratic.GenericSeparationLemmas

namespace OAI

section

/-!
# One polynomial controls all binary linear lifts

For fixed binary dimension, multiply the nonzero obstructions for the finitely
many sets of `3r + 1` nonzero inputs.  A nonvanishing specialization then obeys
the alignment bound simultaneously for every binary linear map.  The resulting
polynomial and its degree are chosen before the extension field.
-/

namespace UniqueGamesTheorem.Quadratic

open scoped BigOperators

noncomputable section

/-- An unconditional polynomial exceptional-set certificate for the complete
all-lifts alignment condition.  There is no quantified bound on the maps `g`
outside the conclusion, and no choice of extension field enters `P`. -/
theorem exists_all_lifts_alignment_polynomial (J : Type*) [Fintype J] [DecidableEq J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        ∀ g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F),
          (alignmentEvent (R := ZMod 2) (parameterMap x) g
            (fun t => alignmentRightHandSide (parameterMap x t))).card ≤
              3 * Fintype.card J := by
  classical
  let V := J → ZMod 2
  let Esets := {E : Finset V // (0 : V) ∉ E ∧ E.card = 3 * Fintype.card J + 1}
  have hex (E : Esets) := exists_nonzero_alignment_obstruction
    (fun t : E.val => (t : V)) Subtype.val_injective
    (fun t : E.val => by
      intro hz
      apply E.property.1
      simpa only [hz] using t.property)
    (show 3 * Fintype.card J < Fintype.card E.val by
      simpa only [Fintype.card_coe, E.property.2] using
        Nat.lt_succ_self (3 * Fintype.card J))
  choose p hp hvanish using hex
  let P : MvPolynomial (Fin 3 × J) (ZMod 2) := ∏ E : Esets, p E
  refine ⟨P, Finset.prod_ne_zero_iff.mpr (fun E _ => hp E), ?_⟩
  intro F _ _ _ _ x hP g
  by_contra hbad
  have hlarge : 3 * Fintype.card J + 1 ≤
      (alignmentEvent (R := ZMod 2) (parameterMap x) g
        (fun t => alignmentRightHandSide (parameterMap x t))).card := by omega
  obtain ⟨E, hsub, hcard⟩ := Finset.exists_subset_card_eq hlarge
  have hzero : (0 : V) ∉ E := by
    intro hz
    have hmem := hsub hz
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.1 rfl
  let E' : Esets := ⟨E, hzero, hcard⟩
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    MvPolynomial.eval₂Hom (algebraMap (ZMod 2) F) x
  let c : E → F := fun t => alignmentRightHandSide (parameterMap x (t : V))
  let a : (Fin 3 × J) → F :=
    fun ij => g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  have hc (t : E) :
      c t ^ 2 = ρ (∏ i : Fin 3, universalLinearForm (t : V) i) := by
    exact alignmentRightHandSide_sq x t
  have ha (t : E) : c t = ∑ ij, ρ
      (universalAlignmentColumn (fun t : E => (t : V)) ij t) * a ij := by
    have hmem := hsub t.property
    simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have ht := hmem.2
    calc
      c t = ∑ i, parameterMap x (t : V) i * g (t : V) i := ht.symm
      _ = _ := dot_parameter_lift x g t
  have hz : ρ (p E') = 0 := hvanish E' F ρ c a hc ha
  apply hP
  change ρ P = 0
  simp only [P, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ E') hz

end

end UniqueGamesTheorem.Quadratic

end

section

/-! Exact correspondence between uniform field entries and all binary-linear maps. -/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

/-- Every binary-linear map is determined by its freely chosen field-valued
basis entries, with no rejection or nonuniform multiplicity. -/
def parameterMapEquiv : ((Fin 3 × J) → F) ≃
    ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := parameterMap
  invFun g ij := g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  left_inv x := by
    funext ij
    exact parameterMap_basis x ij.2 ij.1
  right_inv g := by
    apply (Pi.basisFun (ZMod 2) J).ext
    intro j
    funext i
    exact parameterMap_basis _ j i

omit [CharP F 2] in
theorem parameterMap_event_card
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    Nat.card {x : (Fin 3 × J) → F // event (parameterMap x)} =
      Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} := by
  exact Nat.card_congr ((parameterMapEquiv (F := F) (J := J)).subtypeEquiv
    (p := fun x => event (parameterMap x)) (q := event) (fun _ => Iff.rfl))

variable [Fintype F]

omit [CharP F 2] in
/-- The uniform probability on field entries is literally the uniform
probability on all linear maps.  This is the denominator used before
conditioning on injectivity in `UniformSubspaces.bad_subspace_bound`. -/
theorem parameterMap_event_probability
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    (finiteAssignmentProbability (fun x => event (parameterMap x)) : ℚ) =
      (Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} : ℚ) /
        Nat.card ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) := by
  classical
  have hall := Nat.card_congr (parameterMapEquiv (F := F) (J := J))
  have hevent := parameterMap_event_card event
  rw [← hevent, ← hall]
  simp [finiteAssignmentProbability, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext assignment
  simp

end

end UniqueGamesTheorem.Quadratic

end

section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

namespace UniqueGamesTheorem.Quadratic

open MvPolynomial
open scoped BigOperators

noncomputable section

variable (J : Type*) [Fintype J]

def nonzeroBinaryInputs : Finset (J → ZMod 2) := by
  classical
  exact Finset.univ.erase 0

def distinctNonzeroBinaryPairs : Finset ((J → ZMod 2) × (J → ZMod 2)) := by
  classical
  exact Finset.univ.filter (fun tu => tu.1 ≠ 0 ∧ tu.2 ≠ 0 ∧ tu.1 ≠ tu.2)

def separationPolynomial : MvPolynomial (Fin 3 × J) (ZMod 2) :=
  (∏ t ∈ nonzeroBinaryInputs J, universalLinearForm t 0) *
    ∏ tu ∈ distinctNonzeroBinaryPairs J, universalPairMinor tu.1 tu.2

theorem separationPolynomial_ne_zero : separationPolynomial J ≠ 0 := by
  classical
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact universalLinearForm_zero_ne_zero t
      (Finset.mem_erase.mp ht).1
  · apply Finset.prod_ne_zero_iff.mpr
    intro tu htu
    have h := (Finset.mem_filter.mp htu).2
    exact universalPairMinor_ne_zero tu.1 tu.2 h.1 h.2.1 h.2.2

variable {J}

/-- Outside the zero set of the fixed separation polynomial, the actual
parametrization is injective and no two distinct nonzero inputs have
proportional images. The same polynomial works over every characteristic-two
field. -/
theorem parameterMap_separated_of_eval_ne_zero
    {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
    (x : (Fin 3 × J) → F)
    (hx : eval₂ (algebraMap (ZMod 2) F) x (separationPolynomial J) ≠ 0) :
    Function.Injective (parameterMap x) ∧
      ∀ t u : J → ZMod 2, t ≠ 0 → u ≠ 0 →
        (∃ a : F, parameterMap x t = a • parameterMap x u) → t = u := by
  classical
  let ρ : MvPolynomial (Fin 3 × J) (ZMod 2) →+* F :=
    eval₂Hom (algebraMap (ZMod 2) F) x
  have hprod :
      (∏ t ∈ nonzeroBinaryInputs J, ρ (universalLinearForm t 0)) *
        (∏ tu ∈ distinctNonzeroBinaryPairs J, ρ (universalPairMinor tu.1 tu.2)) ≠ 0 := by
    change ρ (separationPolynomial J) ≠ 0 at hx
    simpa only [separationPolynomial, map_mul, map_prod] using hx
  have hlinear := (mul_ne_zero_iff.mp hprod).1
  have hminor := (mul_ne_zero_iff.mp hprod).2
  have hnonzero (t : J → ZMod 2) (ht : t ≠ 0) : parameterMap x t 0 ≠ 0 := by
    have hmem : t ∈ nonzeroBinaryInputs J := by
      simp [nonzeroBinaryInputs, ht]
    have h := Finset.prod_ne_zero_iff.mp hlinear t hmem
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t 0) ≠ 0 at h
    rwa [eval_universalLinearForm] at h
  constructor
  · intro t u htu
    by_contra hne
    have hz : parameterMap x (t - u) = 0 := by
      rw [map_sub, htu, sub_self]
    exact hnonzero (t - u) (sub_ne_zero.mpr hne) (congrFun hz 0)
  · intro t u ht hu hprop
    by_contra hne
    have hmem : (t, u) ∈ distinctNonzeroBinaryPairs J := by
      simp [distinctNonzeroBinaryPairs, ht, hu, hne]
    have hnz := Finset.prod_ne_zero_iff.mp hminor (t, u) hmem
    obtain ⟨a, ha⟩ := hprop
    apply hnz
    apply universalPairMinor_eq_zero_of_proportional t u ρ a
    intro i
    change eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm t i) =
      a * eval₂ (algebraMap (ZMod 2) F) x (universalLinearForm u i)
    rw [eval_universalLinearForm, eval_universalLinearForm]
    simpa only [Pi.smul_apply, smul_eq_mul] using congrFun ha i

end

end UniqueGamesTheorem.Quadratic

end

section

/-!
# A fixed polynomial certifies genuine all-lifts generic subspaces

The certificate is constructed from binary input sets and is independent of
the extension field.  It combines injectivity, pairwise nonproportionality,
and the simultaneous alignment bound, then transports the latter to the
actual image subspace.  The finite-field exceptional probability tends to
zero with field size using a fixed finite numerator.
-/

namespace UniqueGamesTheorem.Quadratic

noncomputable section

theorem exists_genericity_polynomial (J : Type*) [Fintype J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range := by
  classical
  obtain ⟨A, hA, halign⟩ := exists_all_lifts_alignment_polynomial J
  refine ⟨separationPolynomial J * A, mul_ne_zero (separationPolynomial_ne_zero J) hA, ?_⟩
  intro F _ _ _ _ x hP
  rw [MvPolynomial.eval₂_mul] at hP
  have hparts := mul_ne_zero_iff.mp hP
  have hsep := parameterMap_separated_of_eval_ne_zero x hparts.1
  refine ⟨hsep.1, isGeneric_range_of_injective (parameterMap x) hsep.1 hsep.2 ?_⟩
  intro g
  simpa only [Module.finrank_fintype_fun_eq_card] using halign F x hparts.2 g

/-- The total exceptional probability for random coordinate entries is
`O_r(1 / |F|)`, with a positive integer numerator fixed before `F` is chosen.
Both noninjectivity and failure of the all-lifts image property are counted. -/
theorem exists_genericity_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
          ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) ≤
            (D : ℚ≥0) / Fintype.card F := by
  classical
  obtain ⟨P, hP, hgood⟩ := exists_genericity_polynomial J
  refine ⟨P.totalDegree + 1, Nat.succ_pos _, ?_⟩
  intro F _ _ _ _
  have h := finiteAssignmentProbability_le_of_polynomial
    (algebraMap (ZMod 2) F) (algebraMap (ZMod 2) F).injective P hP
    (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range))
    (by
      intro x hx
      by_contra hne
      exact hx (hgood F x hne))
  apply h.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Nat.le_succ P.totalDegree

end

end UniqueGamesTheorem.Quadratic

end

section

namespace UniqueGamesTheorem.Quadratic

variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The field trace to the binary prime field. -/
noncomputable abbrev traceBinary : F →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) F

omit [CharP F 2] in
theorem trace_square (x : F) : traceBinary (x ^ 2) = traceBinary x := by
  simpa only [traceBinary, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card] using
    Algebra.trace_eq_of_algEquiv
      (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) F) x

/-- Moving a square from the first factor through the trace. -/
theorem trace_square_mul (t c : F) :
    traceBinary (t ^ 2 * c) = traceBinary (t * squareRoot c) := by
  calc
    traceBinary (t ^ 2 * c) = traceBinary ((t * squareRoot c) ^ 2) := by
      rw [mul_pow, squareRoot_sq]
    _ = traceBinary (t * squareRoot c) := trace_square _

omit [CharP F 2] in
/-- The trace pairing detects every nonzero field element. -/
theorem trace_mul_vanish_iff (a : F) :
    (∀ t : F, traceBinary (t * a) = 0) ↔ a = 0 := by
  constructor
  · intro h
    apply (traceForm_nondegenerate (ZMod 2) F).1 a
    intro t
    simpa only [Algebra.traceForm_apply, mul_comm] using h t
  · rintro rfl
    simp

theorem trace_quadratic_vanish_iff (a c : F) :
    (∀ t : F, traceBinary (t * a + t ^ 2 * c) = 0) ↔ a = squareRoot c := by
  have heq (t : F) :
      traceBinary (t * a + t ^ 2 * c) = traceBinary (t * (a + squareRoot c)) := by
    rw [map_add, trace_square_mul, mul_add, map_add]
  simp_rw [heq]
  rw [trace_mul_vanish_iff, add_eq_zero_iff_eq_neg, CharTwo.neg_eq]

end UniqueGamesTheorem.Quadratic

end

end OAI
