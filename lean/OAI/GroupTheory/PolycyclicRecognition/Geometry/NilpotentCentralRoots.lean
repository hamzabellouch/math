import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentClassBound
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrderUnipotent

namespace OAI

/-! # Isolated centers in torsion-free nilpotent groups

If a nonzero power of an element is central, its unipotent action on a maximal
abelian normal subgroup has finite order and is trivial. The element belongs
to that abelian subgroup, where torsion freeness makes roots unique. Thus it
is central, and the quotient by the center is torsion free.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type} [Group G] [Group.IsNilpotent G]

theorem nilpotent_mem_center_of_pow_mem_center
    (hG : HasNoNontrivialTorsion G) (g : G) {n : ℕ} (hn : n ≠ 0)
    (hgn : g ^ n ∈ Subgroup.center G) : g ∈ Subgroup.center G := by
  obtain ⟨A, hAn, hAa, hmax⟩ := exists_maximal_abelian_normal_subgroup G
  let := hAn
  let := hAa
  have hA : HasNoNontrivialTorsion A := by
    intro a k hk hak
    apply Subtype.ext
    exact hG a k hk (congrArg Subtype.val hak)
  let ρ := rationalConjugationLinear A
  have hcentral : g ^ n ∈ (rationalConjugationLinear A).ker := by
    rw [rationalConjugationLinear_ker A hA]
    exact Subgroup.center_le_centralizer _ hgn
  have hpow : ρ g ^ n = 1 := by
    rw [← map_pow]
    exact hcentral
  have hid : ρ g = 1 := rationalUnipotent_eq_one_of_pow_eq_one (ρ g)
    (rationalConjugationDifference_nilpotent A g) hn hpow
  have hgA : g ∈ A := by
    have hgker : g ∈ (rationalConjugationLinear A).ker := hid
    rw [rationalConjugationLinear_ker A hA,
      centralizer_eq_of_maximal_abelian_normal G A hmax] at hgker
    exact hgker
  let a : A := ⟨g, hgA⟩
  let : IsMulTorsionFree A := isMulTorsionFree_iff_not_isOfFinOrder.mpr (by
    intro b hb hfin
    exact hb (hA b (orderOf b) (ne_of_gt hfin.orderOf_pos) (pow_orderOf_eq_one b)))
  apply Subgroup.mem_center_iff.mpr
  intro x
  have hxpow : (MulAut.conjNormal (H := A) x a) ^ n = a ^ n := by
    rw [← map_pow]
    apply Subtype.ext
    change x * (g ^ n) * x⁻¹ = g ^ n
    rw [Subgroup.mem_center_iff.mp hgn x, mul_inv_cancel_right]
  have hxa : MulAut.conjNormal (H := A) x a = a := pow_left_injective hn hxpow
  exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hxa)

theorem nilpotent_centerQuotient_torsionFree (hG : HasNoNontrivialTorsion G) :
    HasNoNontrivialTorsion (G ⧸ Subgroup.center G) := by
  intro q n hn hqn
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) q
  apply (QuotientGroup.eq_one_iff g).mpr
  apply nilpotent_mem_center_of_pow_mem_center hG g hn
  apply (QuotientGroup.eq_one_iff (g ^ n)).mp
  change (QuotientGroup.mk' (Subgroup.center G)) (g ^ n) = 1
  simpa only [map_pow] using hqn

end PolycyclicRecognition

end

end OAI
