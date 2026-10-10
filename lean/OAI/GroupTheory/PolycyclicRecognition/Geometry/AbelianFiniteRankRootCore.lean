import OAI.GroupTheory.PolycyclicRecognition.Geometry.AbelianRootGenerators
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentQuotientRank
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ScalarExtendedH2CrossProduct
import Mathlib.GroupTheory.Torsion

namespace OAI

/-! # A finite root core for an abelian group with arbitrary torsion

Only finite rational rank is needed. Quotienting by the actual torsion
subgroup gives a torsion-free root core, and finite lifts suffice upstairs.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped TensorProduct
variable {A : Type} [CommGroup A]

theorem abelian_finiteRank_rootCore [Module.Finite ℚ (RationalAbelianSpace A)] :
    ∃ H : Subgroup A, H.FG ∧ ∀ a, ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  let T := CommGroup.torsion A
  let Q := A ⧸ T
  let q : A →* Q := QuotientGroup.mk' T
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective T
  let f := q.toAdditive.toIntLinearMap
  have hf : Function.Surjective f := hq
  let : Module.Finite ℚ (RationalAbelianSpace Q) :=
    Module.Finite.of_surjective (f.baseChange ℚ) (f.baseChange_surjective ℚ hf)
  have htQ : HasNoNontrivialTorsion Q := by
    intro a n hn ha
    exact (pow_eq_one_iff_left hn).mp ha
  obtain ⟨L, hL, hroot⟩ := abelian_exists_fg_subgroup_containing_powers htQ
  let P := L.comap q
  let : Group.FG L := (Group.fg_iff_subgroup_fg L).mpr hL
  obtain ⟨F, hF, hFq⟩ := exists_fg_subgroup_surjective
    (quotientSubgroupMap q L) (quotientSubgroupMap_surjective q hq L)
  let H := F.map P.subtype
  refine ⟨H, fg_subgroup_map hF P.subtype, ?_⟩
  intro a
  obtain ⟨n, hn, hna⟩ := hroot (q a)
  have hna' : q (a ^ n) ∈ L := by simpa only [map_pow] using hna
  obtain ⟨x, hx⟩ := hFq ⟨q (a ^ n), hna'⟩
  let b : A := x.val.val
  have hb : b ∈ H := ⟨x.val, x.property, rfl⟩
  have hqb : q b = q (a ^ n) := congrArg Subtype.val hx
  have ht : a ^ n * b⁻¹ ∈ T := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (a ^ n * b⁻¹) = 1
    rw [map_mul, map_inv, hqb, mul_inv_cancel]
  obtain ⟨m, hm, he⟩ := ht.exists_pow_eq_one
  have hab : a ^ (n * m) = b ^ m := by
    rw [mul_pow, inv_pow, mul_inv_eq_one, ← pow_mul] at he
    exact he
  refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
  rw [hab]
  exact H.pow_mem hb m

end PolycyclicRecognition

end

end OAI
