import OAI.Algebra.Universal.Congruence
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Setoid.Basic

namespace OAI

/-!
# Congruences of coset actions

The full congruence lattice of the left action on a finite group's cosets is the
subgroup interval above the stabilizer. No normality assumption is needed.
-/

namespace FiniteCongruence

noncomputable section
variable {G : Type} [Group G] [Fintype G] (H : Subgroup G)

/-- One unary operation for each element of G; no omitted operations. -/
def cosetAlgebra : Algebra (G ⧸ H) where
  numOps := Fintype.card G
  arity := fun _ => 1
  op := fun i x => (Fintype.equivFin G).symm i • x 0

lemma compatible_iff_invariant (r : Setoid (G ⧸ H)) :
    Compatible (cosetAlgebra H) r ↔
      ∀ g : G, ∀ x y : G ⧸ H, r x y → r (g • x) (g • y) := by
  constructor
  · intro hr g x y hxy
    have h := hr ((Fintype.equivFin G) g) (fun _ => x) (fun _ => y) (fun _ => hxy)
    simpa [cosetAlgebra] using h
  · intro hr i x y hxy
    change Fin 1 → G ⧸ H at x y
    change ∀ j : Fin 1, r (x j) (y j) at hxy
    exact hr ((Fintype.equivFin G).symm i) (x 0) (y 0) (hxy 0)

abbrev base : G ⧸ H := (1 : G)

/-- The subgroup determined by the class of the identity coset. -/
def subgroupOf (r : Congruence (cosetAlgebra H)) : Subgroup G where
  carrier := {g | r.val (base H) (g • base H)}
  one_mem' := by
    change r.val (base H) ((1 : G) • base H)
    rw [one_smul]
  mul_mem' := by
    intro a b ha hb
    have hab := (compatible_iff_invariant H r.val).mp r.property a _ _ hb
    simpa [mul_smul] using r.val.trans ha hab
  inv_mem' := by
    intro a ha
    have h := (compatible_iff_invariant H r.val).mp r.property a⁻¹ _ _ ha
    simpa using r.val.symm h

lemma le_subgroupOf (r : Congruence (cosetAlgebra H)) : H ≤ subgroupOf H r := by
  intro g hg
  have heq : (g : G ⧸ H) = (1 : G) := QuotientGroup.eq.mpr (by simpa using H.inv_mem hg)
  change r.val (base H) (g • base H)
  have hbase : g • base H = base H := by simpa [base] using heq
  rw [hbase]

/-- The canonical quotient-set map exists without a normality assumption. -/
def quotientMap (K : Subgroup G) (h : H ≤ K) : G ⧸ H → G ⧸ K :=
  Quotient.map' id (fun _ _ hxy => QuotientGroup.leftRel_apply.mpr
    (h (QuotientGroup.leftRel_apply.mp hxy)))

omit [Fintype G] in
lemma quotientMap_mk (K : Subgroup G) (h : H ≤ K) (g : G) :
    quotientMap H K h (g : G ⧸ H) = (g : G ⧸ K) := rfl

omit [Fintype G] in
lemma quotientMap_smul (K : Subgroup G) (h : H ≤ K) (g : G) (x : G ⧸ H) :
    quotientMap H K h (g • x) = g • quotientMap H K h x := by
  induction x using Quotient.inductionOn' with
  | h a => rfl

/-- Pullback of equality on G/K, hence an actual equivalence relation on G/H. -/
def congruenceOf (K : Subgroup G) (h : H ≤ K) : Congruence (cosetAlgebra H) :=
  ⟨Setoid.ker (quotientMap H K h), (compatible_iff_invariant H _).mpr (by
    intro g x y hxy
    change quotientMap H K h (g • x) = quotientMap H K h (g • y)
    rw [quotientMap_smul, quotientMap_smul]
    exact congrArg (fun q : G ⧸ K => g • q) hxy)⟩

lemma congruenceOf_mk (K : Subgroup G) (h : H ≤ K) (a b : G) :
    (congruenceOf H K h).val (a : G ⧸ H) (b : G ⧸ H) ↔ a⁻¹ * b ∈ K := by
  change ((a : G ⧸ K) = (b : G ⧸ K)) ↔ _
  exact QuotientGroup.eq

lemma invariant_mk_iff (r : Congruence (cosetAlgebra H)) (a b : G) :
    r.val (a : G ⧸ H) (b : G ⧸ H) ↔ a⁻¹ * b ∈ subgroupOf H r := by
  have inv := (compatible_iff_invariant H r.val).mp r.property
  constructor
  · intro hab
    have h := inv a⁻¹ _ _ hab
    change r.val (base H) ((a⁻¹ * b) • base H)
    simpa [base, MulAction.Quotient.smul_coe, smul_eq_mul] using h
  · intro hab
    change r.val (base H) ((a⁻¹ * b) • base H) at hab
    have h := inv a _ _ hab
    simpa [base, mul_smul, MulAction.Quotient.smul_coe, smul_eq_mul] using h

lemma subgroupOf_congruenceOf (K : Subgroup G) (h : H ≤ K) :
    subgroupOf H (congruenceOf H K h) = K := by
  ext g
  change (congruenceOf H K h).val (base H) (g • base H) ↔ g ∈ K
  simpa [base, MulAction.Quotient.smul_coe, smul_eq_mul] using congruenceOf_mk H K h 1 g

lemma congruenceOf_subgroupOf (r : Congruence (cosetAlgebra H)) :
    congruenceOf H (subgroupOf H r) (le_subgroupOf H r) = r := by
  apply Subtype.ext
  ext x y
  induction x using Quotient.inductionOn' with
  | h a =>
    induction y using Quotient.inductionOn' with
    | h b =>
      exact (congruenceOf_mk H _ _ a b).trans (invariant_mk_iff H r a b).symm

/-- The full congruence lattice of the coset algebra is order-isomorphic to the subgroup interval. -/
def coset_action_correspondence :
    Congruence (cosetAlgebra H) ≃o Set.Icc H (⊤ : Subgroup G) where
  toFun r := ⟨subgroupOf H r, le_subgroupOf H r, le_top⟩
  invFun K := congruenceOf H K.val K.property.1
  left_inv r := congruenceOf_subgroupOf H r
  right_inv K := by
    apply Subtype.ext
    exact subgroupOf_congruenceOf H K.val K.property.1
  map_rel_iff' := by
    intro r s
    change subgroupOf H r ≤ subgroupOf H s ↔ r.val ≤ s.val
    constructor
    · intro h x y hxy
      induction x using Quotient.inductionOn' with
      | h a =>
        induction y using Quotient.inductionOn' with
        | h b => exact (invariant_mk_iff H s a b).mpr (h ((invariant_mk_iff H r a b).mp hxy))
    · intro h g hg
      exact h hg

/-- The finite coset algebra realizes the full subgroup interval. -/
theorem coset_action_correspondence_exists :
    Nonempty (Congruence (cosetAlgebra H) ≃o Set.Icc H (⊤ : Subgroup G)) :=
  ⟨coset_action_correspondence H⟩

end
end FiniteCongruence

end OAI
