import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraicDegreeOverTranscendentalField
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalTorsionEigenvalues

namespace OAI

/-! # Uniform degree bounds over finitely generated coefficient fields -/

noncomputable section
namespace PolycyclicRecognition
open Polynomial IntermediateField

theorem rational_minpoly_degree_le_over_transcendental_field
    {K E I : Type*} [Field K] [CharZero K] [Field E] [CharZero E]
    [Algebra K E] [IsScalarTower ℚ K E]
    (t : I → K) (ht : AlgebraicIndependent ℚ t)
    [FiniteDimensional (adjoin ℚ (Set.range t)) K]
    (z : E) (hi : IsIntegral ℚ z) :
    (minpoly ℚ z).natDegree ≤
      Module.finrank (adjoin ℚ (Set.range t)) K * (minpoly K z).natDegree := by
  let B := adjoin ℚ (Set.range t)
  let L := adjoin K {z}
  have hiz : IsIntegral K z := hi.tower_top
  let : FiniteDimensional K L := adjoin.finiteDimensional hiz
  let : FiniteDimensional B L := Module.Finite.trans K L
  let zL : L := AdjoinSimple.gen K z
  have hiL : IsIntegral ℚ zL := by
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℚ L E)
      (algebraMap L E).injective).mp
    exact hi
  let C := adjoin ℚ {zL}
  let : FiniteDimensional ℚ C := adjoin.finiteDimensional hiL
  let : Algebra.IsAlgebraic ℚ C := Algebra.IsAlgebraic.of_finite ℚ C
  have hb := constants_rank_le_in_field_extension (F := ℚ) (K := K) (E := L) (L := C) t ht
  have hdC : Module.finrank ℚ C = (minpoly ℚ z).natDegree := by
    rw [adjoin.finrank hiL]
    exact congrArg Polynomial.natDegree (minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ L E)
      (algebraMap L E).injective zL).symm
  have hdL : Module.finrank B L = Module.finrank B K * (minpoly K z).natDegree := by
    rw [← Module.finrank_mul_finrank B K L, adjoin.finrank hiz]
  rw [← Module.finrank_eq_rank, hdC, hdL] at hb
  exact_mod_cast hb

theorem exists_rational_degree_bound_for_roots
    (K : Type*) [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K] :
    ∃ D : ℕ, ∀ (E : Type*) [Field E] [CharZero E]
      [Algebra K E] [IsScalarTower ℚ K E], ∀ (p : K[X]) (z : E),
      p ≠ 0 → aeval z p = 0 → IsIntegral ℚ z →
      (minpoly ℚ z).natDegree ≤ D * p.natDegree := by
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis ℚ K
  let B := adjoin ℚ (Set.range ((↑) : s → K))
  have : Algebra.IsAlgebraic B K := hs.isAlgebraic_field
  have : Algebra.EssFiniteType B K := Algebra.EssFiniteType.of_comp ℚ B K
  let : FiniteDimensional B K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨Module.finrank B K, ?_⟩
  intro E _ _ _ _ p z hp he hi
  exact (rational_minpoly_degree_le_over_transcendental_field ((↑) : s → K) hs.1 z hi).trans
    (Nat.mul_le_mul_left _ (natDegree_le_of_dvd (minpoly.dvd K z he) hp))

end PolycyclicRecognition

end

end OAI
