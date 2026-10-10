import Mathlib
import OAI.Computability.MaxCut.Games.HarmonicLoss
import OAI.Computability.MaxCut.Games.GenericPolynomial

namespace OAI

noncomputable section

/-! A single finite polynomial certifies injectivity and pair separation of
the actual binary-linear parametrization. -/

namespace MaxCutGames.Quadratic

section

open MvPolynomial
open scoped BigOperators

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

/-!
# Passing genericity from a parametrization to its actual image

An injective binary-linear parametrization identifies its domain with the
image subspace. The universal quantifier over linear lifts is transported
by composition, and alignment-event cardinalities agree exactly.
-/

section

open scoped BigOperators

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

/-!
# Finite-field polynomial exceptional events

The nonzero polynomial obstruction for each fixed input set gives a uniform
bound over all linear lifts.  Its coefficients lie in the binary prime field,
so its degree is fixed before the extension field is chosen.  The theorems
below keep this order explicit and combine finitely many obstructions without
any union over maps.
-/

section

open scoped BigOperators

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

/-!
# Polynomial exceptional events on arbitrary finite variable sets

Reindexing the variable set transports both the polynomial and the uniform
assignment space. Thus the checked finite-field zero bound applies directly
to the three-by-r «variables» in the genericity proof, without changing the
degree or taking a union over possible linear lifts.
-/

section

open scoped BigOperators

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

/-!
# A fixed polynomial certifies genuine all-lifts generic subspaces

The certificate is constructed from binary input sets and is independent of
the extension field.  It combines injectivity, pairwise nonproportionality,
and the simultaneous alignment bound, then transports the latter to the
actual image subspace.  The finite-field exceptional probability tends to
zero with field size using a fixed finite numerator.
-/

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

/-! Exact correspondence between uniform field entries and all binary-linear maps. -/

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
  simp [finiteAssignmentProbability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ] ; congr 1 ; ext x ; simp

end MaxCutGames.Quadratic

/-!
Uniform injective parameter maps induce the uniform law on subspaces of the
specified rank.  The proof uses actual transitivity of ambient linear
automorphisms on injections, not an assumed distributional premise.
-/

section

open scoped BigOperators
open Module
open MaxCutGames.Gadget.Orientation

namespace MaxCutGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- A linear parameter map with its injectivity proof. -/
def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

omit [FiniteDimensional K W] in
/-- Every two injections are carried to each other by an automorphism of the
ambient space: extend the isomorphism between their two images. -/
theorem injection_transitive (J₁ J₂ : Injection K V W) :
    ∃ a : W ≃ₗ[K] W, a • J₁ = J₂ := by
  let e₁ := LinearEquiv.ofInjective J₁.val J₁.property
  let e₂ := LinearEquiv.ofInjective J₂.val J₂.property
  let e : LinearMap.range J₁.val ≃ₗ[K] LinearMap.range J₂.val := e₁.symm.trans e₂
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext x
  have h := (ha (e₁ x)).symm
  change a (J₁.val x) = ((e₂ (e₁.symm (e₁ x))) : W) at h
  change a (J₁.val x) = J₂.val x
  simpa only [LinearEquiv.symm_apply_apply, e₂, LinearEquiv.ofInjective_apply] using h

/-- The image has the dimension of the parameter space. -/
def image (J : Injection K V W) : RankSpace K W (finrank K V) :=
  ⟨LinearMap.range J.val, LinearMap.finrank_range_of_inj J.property⟩

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem image_action (a : W ≃ₗ[K] W) (J : Injection K V W) :
    image (a • J) = a • image J := by
  apply Subtype.ext
  exact LinearMap.range_comp J.val a.toLinearMap

variable [Fintype (W ≃ₗ[K] W)] [Fintype (Injection K V W)]
    [Fintype (RankSpace K W (finrank K V))]

/-- Exact uniform image law, conditional only on injectivity of the map. -/
theorem mean_image (J₀ : Injection K V W) (f : RankSpace K W (finrank K V) → ℚ) :
    (∑ J : Injection K V W, f (image J)) / Fintype.card (Injection K V W) =
      (∑ S : RankSpace K W (finrank K V), f S) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  have h := mean_action J₀ (injection_transitive J₀) (fun J => f (image J))
  simp_rw [image_action] at h
  exact h.symm.trans (mean_oriented_subspace (image J₀) f)

/-- Indicator specialization of the exact law, without assuming genericity
or independence of a subsequently chosen lift. -/
theorem bad_image_count_ratio (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) :
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) /
        Fintype.card (Injection K V W) =
      (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  classical
  have h := mean_image J₀ (fun S => if Bad S then 1 else 0)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- An unconditional bad-parameter count bound transfers after conditioning
on injectivity, paying exactly the usual `1/(1-β)` factor.  The premises are
ordinary count inequalities and can come from polynomial union bounds. -/
theorem bad_subspace_bound (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) (α β : ℚ) (hα : 0 ≤ α) (hβ : β < 1)
    (hbad : (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) ≤
      α * Nat.card (V →ₗ[K] W))
    (hinj : (1 - β) * Nat.card (V →ₗ[K] W) ≤ Fintype.card (Injection K V W)) :
    (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) ≤ α / (1 - β) := by
  rw [← bad_image_count_ratio J₀ Bad]
  have : Nonempty (Injection K V W) := ⟨J₀⟩
  have hi : (0 : ℚ) < Fintype.card (Injection K V W) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  apply (div_le_div_iff₀ hi hd).mpr
  calc
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) * (1 - β) ≤
        (α * Nat.card (V →ₗ[K] W)) * (1 - β) :=
      mul_le_mul_of_nonneg_right hbad hd.le
    _ = α * ((1 - β) * Nat.card (V →ₗ[K] W)) := by ring
    _ ≤ α * Fintype.card (Injection K V W) := mul_le_mul_of_nonneg_left hinj hα

end MaxCutGames.Quadratic.UniformSubspaces
end

/-!
The polynomial exceptional-event bound is transported first to all binary
linear parameter maps and then, by proved uniformity conditional on
injectivity, to the actual finite Grassmannian.  The same argument supplies
a generic subspace, rather than presupposing that one exists.
-/

open Module
open MaxCutGames.Gadget.Orientation

namespace MaxCutGames.Quadratic

private theorem conditioning_counts_inline_GenericSubspaceProbability {A : Type*} [Fintype A] [Nonempty A]
    (P Q : A → Prop) (α : ℚ) (hα : α < 1)
    (hbad : (Nat.card {a : A // ¬(P a ∧ Q a)} : ℚ) / Nat.card A ≤ α) :
    (∃ a : A, P a ∧ Q a) ∧
      (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤ α * Nat.card A ∧
      (1 - α) * Nat.card A ≤ (Nat.card {a : A // P a} : ℚ) := by
  classical
  have hpos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hbadCount := (div_le_iff₀ hpos).mp hbad
  have hgood : ∃ a : A, P a ∧ Q a := by
    by_contra h
    have hall : ∀ a : A, ¬(P a ∧ Q a) := fun a ha => h ⟨a, ha⟩
    have hcard : Nat.card {a : A // ¬(P a ∧ Q a)} = Nat.card A := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
    rw [hcard, div_self hpos.ne'] at hbad
    exact (not_le_of_gt hα) hbad
  have hnoninj : Nat.card {a : A // ¬P a} ≤ Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : A // ¬P a} => (⟨a.1, fun h => a.2 h.1⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hbadInj : Nat.card {a : {a : A // P a} // ¬Q a.1} ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : {a : A // P a} // ¬Q a.1} =>
        (⟨a.1.1, fun h => a.2 h.2⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hpartitionNat : Nat.card {a : A // P a} + Nat.card {a : A // ¬P a} = Nat.card A := by
    have hle := Fintype.card_subtype_le P
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  have hpartition : (Nat.card {a : A // P a} : ℚ) +
      Nat.card {a : A // ¬P a} = Nat.card A := by exact_mod_cast hpartitionNat
  have hn : (Nat.card {a : A // ¬P a} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hnoninj
  have hb : (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hbadInj
  refine ⟨hgood, hb.trans hbadCount, ?_⟩
  linarith

variable {F J : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] [Fintype J]

/-- Both generic-subspace existence and the conditional Grassmannian bound
follow from the single unconditional parameter-map exceptional bound. -/
theorem generic_subspace_and_probability_of_parameter_error (α : ℚ)
    (hα₀ : 0 ≤ α) (hα : α < 1)
    (herror : (finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) : ℚ) ≤ α) :
    (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
      nongenericFraction F (Fintype.card J) ≤ α / (1 - α) := by
  classical
  let V := J → ZMod 2
  let W := Fin 3 → F
  let A := V →ₗ[ZMod 2] W
  let P : A → Prop := fun g => Function.Injective g
  let Q : A → Prop := fun g => IsGeneric g.range
  let : Fintype A := Fintype.ofEquiv ((Fin 3 × J) → F) parameterMapEquiv
  let : Fintype (Submodule (ZMod 2) W) :=
    Fintype.ofInjective (fun S : Submodule (ZMod 2) W => (S : Set W)) SetLike.coe_injective
  let : Fintype (W ≃ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let : Fintype (UniformSubspaces.Injection (ZMod 2) V W) :=
    inferInstanceAs (Fintype {g : A // Function.Injective g})
  let : Fintype (RankSpace (ZMod 2) W (finrank (ZMod 2) V)) :=
    inferInstanceAs (Fintype {S : Submodule (ZMod 2) W // finrank (ZMod 2) S = finrank (ZMod 2) V})
  have hcount : (Nat.card {g : A // ¬(P g ∧ Q g)} : ℚ) / Nat.card A ≤ α := by
    rw [parameterMap_event_probability (fun g : A => ¬(P g ∧ Q g))] at herror
    exact herror
  have hc := conditioning_counts_inline_GenericSubspaceProbability P Q α hα hcount
  obtain ⟨g, hgP, hgQ⟩ := hc.1
  let J₀ : UniformSubspaces.Injection (ZMod 2) V W := ⟨g, hgP⟩
  have hdim : finrank (ZMod 2) V = Fintype.card J :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hfrac := UniformSubspaces.bad_subspace_bound J₀
    (fun S : RankSpace (ZMod 2) W (finrank (ZMod 2) V) => ¬IsGeneric S.1)
    α α hα₀ hα hc.2.1 (by
      rw [← Nat.card_eq_fintype_card]
      exact hc.2.2)
  refine ⟨?_, ?_⟩
  · refine ⟨⟨g.range, ?_⟩, hgQ⟩
    simpa only [V, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_of_inj hgP)
  · rw [← Nat.card_eq_fintype_card] at hfrac
    change nongenericFraction F (finrank (ZMod 2) V) ≤ α / (1 - α) at hfrac
    simpa only [hdim] using hfrac

/-- The exact genericity statement with a positive numerator fixed before
the extension field.  The property quantifies over every binary linear lift. -/
theorem exists_generic_subspace_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        (D : ℚ) / Fintype.card F < 1 →
        (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
          nongenericFraction F (Fintype.card J) ≤
            ((D : ℚ) / Fintype.card F) / (1 - (D : ℚ) / Fintype.card F) := by
  obtain ⟨D, hD, hbound⟩ := exists_genericity_error_numerator J
  refine ⟨D, hD, ?_⟩
  intro F _ _ _ _ hsmall
  apply generic_subspace_and_probability_of_parameter_error ((D : ℚ) / Fintype.card F)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  exact_mod_cast hbound F

/-- A convenient numerical threshold for choosing one field for finitely
many ranks: `α ≤ min(1/2, ε/2)` is sufficient. -/
theorem conditional_error_le_of_small (α ε : ℚ) (hα : 0 ≤ α)
    (hhalf : α ≤ 1 / 2) (hε : α ≤ ε / 2) : α / (1 - α) ≤ ε := by
  have hd : 0 < 1 - α := by linarith
  apply (div_le_iff₀ hd).mpr
  have hε₀ : 0 ≤ ε := by linarith
  have hprod : 0 ≤ ε * (1 / 2 - α) := mul_nonneg hε₀ (by linarith)
  nlinarith

end MaxCutGames.Quadratic

end

end OAI
