import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalSubgroupFiltration
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MaximalAbelianNormal

namespace OAI

/-! # A uniform nilpotency-class bound from integral dimension

A maximal abelian normal subgroup of a nilpotent group is self-centralizing.
The faithful rational conjugation action bounds the lower central series
modulo that subgroup. Its pulled-back rational filtration bounds the remaining
series inside it. Each part has length at most the rational rank.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped IsMulCommutative

variable {G : Type} [Group G]

def rationalConjugationLinear (H : Subgroup G) [H.Normal] [IsMulCommutative H] :
    G →* Module.End ℚ (RationalAbelianSpace H) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (rationalConjugation H)

theorem rationalConjugationLinear_ker (H : Subgroup G) [H.Normal] [IsMulCommutative H]
    (hH : HasNoNontrivialTorsion H) :
    (rationalConjugationLinear H).ker = Subgroup.centralizer (H : Set G) := by
  rw [← rationalConjugation_ker H hH]
  ext g
  change (rationalConjugation H g).toLinearMap = 1 ↔ rationalConjugation H g = 1
  exact ⟨fun h => LinearEquiv.toLinearMap_injective h, fun h => congrArg LinearEquiv.toLinearMap h⟩

theorem nilpotencyClass_le_twice_rationalRank [Group.IsNilpotent G]
    (H : Subgroup G) [H.Normal] [IsMulCommutative H]
    [Module.Finite ℚ (RationalAbelianSpace H)] (hH : HasNoNontrivialTorsion H)
    (hC : Subgroup.centralizer (H : Set G) = H) :
    Group.nilpotencyClass G ≤ 2 * Module.finrank ℚ (RationalAbelianSpace H) := by
  let r := Module.finrank ℚ (RationalAbelianSpace H)
  have hF : linearActionFiltration
      (fun g => (rationalConjugation H g).toLinearMap - 1) r = ⊥ :=
    linearActionFiltration_eq_bot_of_word_zero _ r (rationalConjugationWord_zero_at_rank H)
  have hL : (⊤ : Subgroup G).lowerCentralSeries r ≤ H := by
    rw [← hC, ← rationalConjugationLinear_ker H hH]
    exact lowerCentralSeries_le_ker_of_actionFiltration (rationalConjugationLinear H) r hF
  have hlast : (⊤ : Subgroup G).lowerCentralSeries (r + r) = ⊥ := by
    apply eq_bot_iff.mpr
    exact (lowerCentralSeries_le_rationalSubgroupFiltration H r hL r).trans
      (le_of_eq (rationalSubgroupFiltration_eq_bot H hH hF))
  rw [two_mul]
  exact Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hlast

theorem nilpotencyClass_le_twice_cohomologicalDimension [Group.IsNilpotent G]
    (d : ℕ) [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d] :
    Group.nilpotencyClass G ≤ 2 * d := by
  obtain ⟨A, hAn, hAa, hmax⟩ := exists_maximal_abelian_normal_subgroup G
  let := hAn
  let := hAa
  let := abelian_subgroup_rational_finite d A
  have hA : HasFiniteIntegralCohomologicalDimension A :=
    ⟨d, subgroup_cohomologicalDimension_le A d⟩
  have hr : Module.finrank ℚ (RationalAbelianSpace A) ≤ d :=
    FiniteDimensional.finrank_le_iff_rank_le.mpr (abelian_subgroup_rational_rank_le d A)
  exact (nilpotencyClass_le_twice_rationalRank A hA.torsionFree
    (centralizer_eq_of_maximal_abelian_normal G A hmax)).trans (Nat.mul_le_mul_left 2 hr)

theorem nilpotent_subgroup_class_le (d : ℕ)
    [CategoryTheory.HasProjectiveDimensionLE (trivialIntegral G) d]
    (N : Subgroup G) [Group.IsNilpotent N] : Group.nilpotencyClass N ≤ 2 * d := by
  let := subgroup_cohomologicalDimension_le N d
  exact nilpotencyClass_le_twice_cohomologicalDimension d

end PolycyclicRecognition

end

end OAI
