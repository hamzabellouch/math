import OAI.GroupTheory.PChains.Core
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

namespace PCoreCancellation

variable {X : Type*} [Group X]

/-- The stabilizer of the chain beginning with the trivial subgroup and followed
by the nodes in `l`. -/
def stabilizer (l : List (Subgroup X)) : Subgroup X :=
  Subgroup.normalizer ((⊥ : Subgroup X) : Set X) ⊓
    ⨅ Q ∈ l, Subgroup.normalizer (Q : Set X)

/-- A strict chain of p-subgroups with initial trivial subgroup, stabilized by
`J`. The list records the nontrivial nodes, so its length is the chain length. -/
def Chain (p : ℕ) (J : Subgroup X) :=
  {l : List (Subgroup X) // l.Pairwise (· < ·) ∧
    (∀ Q ∈ l, Q ≠ ⊥ ∧ IsPGroup p Q) ∧ J ≤ stabilizer l}

lemma stabilizer_condition (J : Subgroup X) (l : List (Subgroup X)) :
    J ≤ stabilizer l ↔ ∀ Q ∈ l, J ≤ Subgroup.normalizer (Q : Set X) := by
  simp only [stabilizer, Subgroup.normalizer_eq_top, top_inf_eq, le_iInf_iff]

/-- The trivial subgroup contributes the whole ambient group to the intersection
of normalizers. -/
theorem normalizer_intersection_iff (J : Subgroup X) (s : Finset (Subgroup X)) :
    J ≤ Subgroup.normalizer ((⊥ : Subgroup X) : Set X) ⊓
      (⨅ Q ∈ s, Subgroup.normalizer (Q : Set X)) ↔
      ∀ Q ∈ s, J ≤ Subgroup.normalizer (Q : Set X) := by
  simp only [Subgroup.normalizer_eq_top, top_inf_eq, le_iInf_iff]

variable [Fintype X]

noncomputable instance chainFintype (p : ℕ) (J : Subgroup X) : Fintype (Chain p J) := by
  classical
  letI : Fintype (Subgroup X) :=
    Fintype.ofInjective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  apply Fintype.ofInjective (fun l : Chain p J => l.val.toFinset)
  intro a b hab
  apply Subtype.ext
  have hp : a.val.Perm b.val := (List.perm_ext_iff_of_nodup
    (a.property.1.imp (fun h => ne_of_lt h))
    (b.property.1.imp (fun h => ne_of_lt h))).mpr (by
      intro x
      have hx := congrArg (fun s : Finset (Subgroup X) => x ∈ s) hab
      simpa using hx)
  exact List.Perm.eq_of_pairwise' (a.property.1.imp le_of_lt)
    (b.property.1.imp le_of_lt) hp

/-- The alternating sum over actual strict chains stabilized by `J`. -/
noncomputable def weight (p : ℕ) (J : Subgroup X) : ℤ :=
  ∑ l : Chain p J, (-1 : ℤ) ^ l.val.length

end PCoreCancellation

end OAI
