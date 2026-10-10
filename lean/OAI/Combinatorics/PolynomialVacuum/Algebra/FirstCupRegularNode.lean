import OAI.Combinatorics.PolynomialVacuum.Algebra.CupScalarCompatibility
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalUnitary

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

theorem trainDenominator_fusionProduct (a : ℂ) (X : ℕ → ℂ) (k m : ℕ) :
    trainDenominator (T*a) X k m=fusionProduct a (fun r => X (k+r)) m := by
  induction m generalizing k with
  | zero => simp [trainDenominator,fusionProduct]
  | succ m ih =>
    simp only [trainDenominator,ih,← fusionPair_denominator,fusionProduct,
      Finset.prod_range_succ',Nat.add_zero]
    congr 1
    apply Finset.prod_congr rfl
    intro r hr
    rw [show k+1+r=k+(r+1) by omega]

theorem skipOne_eq_insertOne {α : Type*} (X : ℕ → α) :
    skipOne 0 X=insertOne 0 (X 1) (skipTwo 0 X) := by
  funext j
  simp only [skipOne,insertOne,skipTwo_zero_apply,Nat.not_lt_zero,ite_false]
  split_ifs <;> congr 1 <;> omega

 

theorem naturalPrescription_firstCup_regular {ψ : NatSpectralTensor} {m : ℕ}
    (hψ : LowerExchange ψ (m+1)) (X : ℕ → ℂ) (hX : X 1=T*X 0) :
    naturalPrescription ψ (m+1) 0 X=
      naturalFusion (m+1) 0 (insertOne (m+2) (T*X 0) X) •
        cupLinear 0 (ψ (skipTwo 0 (insertOne (m+2) (T*X 0) X))) := by
  have hx : insertOne (m+2) (T*X 0) X 0=X 0 := by simp [insertOne]
  have he := braidTrain_exchange hψ (T*X 0) (skipTwo 0 X) 0 m (by omega)
  simp only [Nat.zero_add] at he
  have ho : braidTrain (T*X 0) X 2 m * cupLinear 0=
      cupLinear 0 * braidTrain (T*X 0) (skipTwo 0 X) 0 m := by
    exact braidTrain_cup_after 0 2 m (by omega) _ _
  simp only [naturalPrescription,leftFusion,Finset.range_zero,Finset.prod_empty,
    mul_one,Nat.zero_add,Nat.sub_zero,braidTrain,Module.End.mul_apply,hX,siteR_regular,map_smul]
  rw [← Module.End.mul_apply,ho,Module.End.mul_apply,skipOne_eq_insertOne,hX,he,map_smul]
  simp only [naturalFusion,hx,skipTwo_insertOne_after,fusionProduct_insertLast,
    trainDenominator_fusionProduct,Nat.zero_add,← fusionPair_denominator,smul_smul]
  congr 1
  ring

end PolynomialVacuumAlgebra

end OAI
