import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open ResidueHaar

def fourModuli (A D Q B : ℕ) : Fin 4 → ℕ := ![A,D,Q,B]

theorem fourModuli_prod (A D Q B : ℕ) : (∏ i,fourModuli A D Q B i)=A*D*Q*B := by
  simp [fourModuli,Fin.prod_univ_succ]
  ring

theorem fourModuli_pairwise (A D Q B : ℕ)
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B) :
    Pairwise (fun i j => (fourModuli A D Q B i).Coprime (fourModuli A D Q B j)) := by
  rcases hc with ⟨hAD,hAQ,hAB,hDQ,hDB,hQB⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [fourModuli,Nat.coprime_comm] <;> assumption

instance fourModuli_neZero (A D Q B : ℕ) [NeZero A] [NeZero D] [NeZero Q] [NeZero B] :
    ∀ i,NeZero (fourModuli A D Q B i) := by
  intro i
  fin_cases i <;> dsimp [fourModuli] <;> infer_instance

theorem four_unit_joint_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (F : (∀ i,UnitPair (fourModuli A D Q B i)) → ℂ) :
    average (fun z : UnitPair (∏ i,fourModuli A D Q B i) =>
      F (unitPairEquiv _ (fourModuli_pairwise A D Q B hc) z)) = average F :=
  unit_joint_average _ _ F

theorem four_mixed_joint_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (F : (∀ i,MixedPair (fourModuli A D Q B i)) → ℂ) :
    average (fun z : MixedPair (∏ i,fourModuli A D Q B i) =>
      F (mixedPairEquiv _ (fourModuli_pairwise A D Q B hc) z)) = average F :=
  mixed_joint_average _ _ F

theorem four_unit_product_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (f : ∀ i,UnitPair (fourModuli A D Q B i) → ℂ) :
    average (fun z : UnitPair (∏ i,fourModuli A D Q B i) =>
      ∏ i,f i (unitPairEquiv _ (fourModuli_pairwise A D Q B hc) z i)) =
      ∏ i,average (f i) := unit_product_average _ _ f

theorem four_mixed_product_average (A D Q B : ℕ)
    [NeZero A] [NeZero D] [NeZero Q] [NeZero B]
    (hc : A.Coprime D ∧ A.Coprime Q ∧ A.Coprime B ∧
      D.Coprime Q ∧ D.Coprime B ∧ Q.Coprime B)
    (f : ∀ i,MixedPair (fourModuli A D Q B i) → ℂ) :
    average (fun z : MixedPair (∏ i,fourModuli A D Q B i) =>
      ∏ i,f i (mixedPairEquiv _ (fourModuli_pairwise A D Q B hc) z i)) =
      ∏ i,average (f i) := mixed_product_average _ _ f

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
