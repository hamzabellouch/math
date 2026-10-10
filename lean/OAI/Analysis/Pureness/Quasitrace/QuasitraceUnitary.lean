import OAI.Analysis.Pureness.Quasitrace.QuasitracePullback
import Mathlib.Algebra.Star.UnitaryStarAlgAut

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal ComplexOrder
variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
namespace PositiveQuasitrace
variable (T : PositiveQuasitrace D)

lemma selfAdjointValue_sum {ι : Type*} (s : Finset ι) (a : ι → selfAdjoint D)
    (hc : ∀ i ∈ s, ∀ j ∈ s, Commute (a i).1 (a j).1) :
    T.selfAdjointValue (∑ i ∈ s, a i) = ∑ i ∈ s, T.selfAdjointValue (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [T.selfAdjointValue_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, T.selfAdjointValue_add, ih, Finset.sum_insert hi]
    · exact fun j hj k hk => hc j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    · change Commute (a i).1 ((selfAdjoint D).subtype (∑ j ∈ s, a j))
      rw [map_sum]
      exact Commute.sum_right s _ _ fun j hj =>
        hc i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)

lemma map_unitary_conjugate (u : unitary D) (a : Positive D) :
    T (Positive.map (Unitary.conjStarAlgAut ℂ D u).toNonUnitalStarAlgHom a) = T a := by
  let w := (u : D) * CFC.sqrt a.1
  have hl : Positive.starMul w = a := by
    apply Subtype.ext
    change star ((u : D)*CFC.sqrt a.1)*((u : D)*CFC.sqrt a.1) = a.1
    rw [star_mul, (CFC.sqrt_nonneg a.1).star_eq]
    calc
      _ = CFC.sqrt a.1 * (star (u : D)*(u : D)) * CFC.sqrt a.1 := by simp only [mul_assoc]
      _ = a.1 := by rw [Unitary.coe_star_mul_self, mul_one, CFC.sqrt_mul_sqrt_self _ a.2]
  have hr : Positive.mulStar w =
      Positive.map (Unitary.conjStarAlgAut ℂ D u).toNonUnitalStarAlgHom a := by
    apply Subtype.ext
    change ((u : D)*CFC.sqrt a.1)*star ((u : D)*CFC.sqrt a.1) = (u : D)*a.1*star (u : D)
    rw [star_mul, (CFC.sqrt_nonneg a.1).star_eq]
    calc
      _ = (u : D)*(CFC.sqrt a.1*CFC.sqrt a.1)*star (u : D) := by simp only [mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self _ a.2]
  exact (congrArg T.toFun hr).symm.trans ((T.polar w).symm.trans (congrArg T.toFun hl))

lemma complexValue_unitary_conjugate (u : unitary D) (x : D) :
    T.complexValue (Unitary.conjStarAlgAut ℂ D u x) = T.complexValue x :=
  T.complexValue_map T (Unitary.conjStarAlgAut ℂ D u).toNonUnitalStarAlgHom
    (T.map_unitary_conjugate u) x
end PositiveQuasitrace
end CuntzPureness

end

end OAI
