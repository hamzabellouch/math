import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinateRoles

namespace OAI

/-! Exact free-coordinate expansion of the distinguished largest-prime
role. The global largest prime is retained, including the selected divisor. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primeTuple_update_weight (f : ι → Eisenstein) (i : ι) (p : Eisenstein)
    (w : ι → Eisenstein → ℂ) :
    (∏ j, w j (Function.update f i p j)) = w i p*(∏ j ∈ Finset.univ.erase i, w j (f j)) := by
  rw [←Finset.mul_prod_erase Finset.univ (fun j => w j (Function.update f i p j))
    (Finset.mem_univ i),Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem distinguished_tuple_largest_reindex [Nonempty ι]
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    {d : Eisenstein} (hd : primary d) (F : (ι → Eisenstein) → ℂ) :
    (∑ f ∈ (Fintype.piFinset S).filter (fun f => Squarefree ((∏ i, f i)*d)),
      if largestPrimeChoice ((∏ i, f i)*d) ∣ ∏ i, f i then F f else 0) =
      ∑ i, ∑ g ∈ coordinateComplementTuples S i, ∑ p ∈ S i,
        if Squarefree ((∏ j, Function.update g i p j)*d) ∧
          largestPrimeChoice ((∏ j, Function.update g i p j)*d) = p
        then F (Function.update g i p) else 0 := by
  rw [Finset.sum_filter]
  calc
    _ = ∑ f ∈ Fintype.piFinset S, ∑ i,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hs : Squarefree ((∏ j, f j)*d)
      · simpa only [hs,ite_true,true_and] using
          distinguished_largest_coordinate_roles f
            (fun i => hS i (f i) ((Fintype.mem_piFinset.mp hf) i)) hd hs (F f)
      · simp only [hs,false_and,ite_false,Finset.sum_const_zero]
    _ = ∑ i, ∑ f ∈ Fintype.piFinset S,
        if Squarefree ((∏ j, f j)*d) ∧ largestPrimeChoice ((∏ j, f j)*d) = f i
        then F f else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [primeTuple_coordinate_reindex S i]
      rw [Finset.sum_comm]
      simp only [Function.update_self]

end CubicFirstMoment

end

end OAI
