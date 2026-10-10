import OAI.NumberTheory.Jacobsthal.Sieve.ExceptionalResidues

namespace OAI

namespace Erdos970

section

namespace ErdosInverseSpectrum
attribute [local instance] Classical.decEq

theorem exceptional_fraction_sum_bound (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) (T : ℝ) (hT : 0 < T) :
    (∑ p ∈ P,((exceptionalResidues p S T).card : ℝ)/(p : ℝ)) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/T^2 := by
  calc
    _ ≤ ∑ p ∈ P,((p : ℝ)*integerResidueVariance p S)/T^2 :=
      Finset.sum_le_sum (fun p hp => exceptional_fraction_le_variance p (hP p hp).pos S T hT)
    _ = (∑ p ∈ P,(p : ℝ)*integerResidueVariance p S)/T^2 := (Finset.sum_div _ _ _).symm
    _ ≤ _ := div_le_div_of_nonneg_right (prime_variance_large_sieve P hP Q J M S hS hQ) (sq_nonneg _)

theorem exceptional_fraction_average_bound (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (hn : 0 < P.card) (Q J : ℕ) (M : ℤ) (S : Finset ℤ) (hS : S ⊆ Finset.Ico M (M+(J : ℤ)))
    (hQ : ∀ p ∈ P,p ≤ Q) (T : ℝ) (hT : 0 < T) :
    (∑ p ∈ P,((exceptionalResidues p S T).card : ℝ)/(p : ℝ))/(P.card : ℝ) ≤
      (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/((P.card : ℝ)*T^2) := by
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  calc
    _ ≤ ((4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/T^2)/(P.card : ℝ) :=
      div_le_div_of_nonneg_right (exceptional_fraction_sum_bound P hP Q J M S hS hQ T hT) hnR.le
    _ = _ := by ring

theorem exceptional_average_of_survivor_upper (P : Finset ℕ) (hP : ∀ p ∈ P,Nat.Prime p)
    (hn : 0 < P.card) (Q J : ℕ) (hJ : 0 < J) (M : ℤ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Ico M (M+(J : ℤ))) (hQ : ∀ p ∈ P,p ≤ Q)
    (delta V0 C : ℝ) (hd : 0 < delta) (hV : 0 < V0)
    (hm : (S.card : ℝ) ≤ C*(J : ℝ)*V0) :
    (∑ p ∈ P,((exceptionalResidues p S (delta*(J : ℝ)*V0)).card : ℝ)/(p : ℝ))/(P.card : ℝ) ≤
      (4+8*Real.pi^2)*C*((J : ℝ)+(Q : ℝ)^2)/((P.card : ℝ)*delta^2*(J : ℝ)*V0) := by
  have hnR : (0 : ℝ) < P.card := by exact_mod_cast hn
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hT : 0 < delta*(J : ℝ)*V0 := mul_pos (mul_pos hd hJR) hV
  calc
    _ ≤ (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(S.card : ℝ)/
        ((P.card : ℝ)*(delta*(J : ℝ)*V0)^2) := exceptional_fraction_average_bound P hP hn Q J M S hS hQ _ hT
    _ ≤ (4+8*Real.pi^2)*((J : ℝ)+(Q : ℝ)^2)*(C*(J : ℝ)*V0)/
        ((P.card : ℝ)*(delta*(J : ℝ)*V0)^2) := by
      gcongr
    _ = _ := by field_simp

end ErdosInverseSpectrum

end

end Erdos970

end OAI
