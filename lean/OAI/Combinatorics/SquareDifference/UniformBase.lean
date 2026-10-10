import OAI.Combinatorics.SquareDifference.PrimeSetup

namespace OAI

section

open Finset

open scoped BigOperators

namespace SquareDifference

open LiftTheory.SquareDifference

lemma positiveLaw_diagonal_pointwise {V X : Type*} [Fintype V]
    (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (hpos : ∀F,(∀z,0≤F z) → 0≤L F)
    (hm : L (fun _ => 1)=1) (f : X → ℝ) (R : ℝ) (hf : ∀x,|f x|≤R) :
    diagonalIntegral L f≤R^(Fintype.card V) := by
  change L (fun z => ∏v,f (z v))≤_
  calc
    _ ≤ L (fun _ => R^(Fintype.card V)) := by
      apply positiveLaw_mono L hpos
      intro z
      calc
        _ ≤ |∏v,f (z v)| := le_abs_self _
        _ = ∏v,|f (z v)| := abs_prod _ _
        _ ≤ ∏_v : V,R := prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun v _ => hf (z v))
        _ = _ := by rw [prod_const,card_univ]
    _ = _ := by rw [positiveLaw_const,hm,mul_one]

lemma setFunctional_base {J : Type} [Fintype J] [DecidableEq J]
    (p : J → ℕ) [∀j,Fact (p j).Prime] (hinj : Function.Injective p)
    (hp : ∀j,tupleMassThreshold≤(p j:ℝ)) (N : ℕ) (hN : 1≤N) (A : Finset ℕ) :
    setFunctional p N (powerCutoff N sourceBeta) A≤(N:ℝ)^(2*Fintype.card TupleVertex) := by
  have hcop : Pairwise fun i j => (p i).Coprime (p j) := by
    intro i j hij
    exact ((Fact.out : (p i).Prime).coprime_iff_not_dvd.mpr
      (fun h => hij (hinj ((Nat.prime_dvd_prime_iff_eq (Fact.out : (p i).Prime) (Fact.out : (p j).Prime)).mp h))))
  have hpt (x : ResidueSpace p) : |actualTruncatedLift p N (powerCutoff N sourceBeta) (natIndicator A) x|≤(powerCutoff N sourceBeta:ℝ)^2 := by
    simpa only [mul_one] using (PairBridge.actualLift_pointwise_bound p hcop N (powerCutoff N sourceBeta) (by omega) (natIndicator A) 1 (by norm_num) (fun n _ => natIndicator_bound A n) x)
  have hh := positiveLaw_diagonal_pointwise (productTupleLaw p) (tensorLaw_nonneg (fun j => tupleLaw (p:=p j)) (fun _ => tupleLaw_nonneg))
    (productTupleLaw_probability p hp) (actualTruncatedLift p N (powerCutoff N sourceBeta) (natIndicator A))
    ((powerCutoff N sourceBeta:ℝ)^2) hpt
  apply hh.trans
  rw [←pow_mul]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast powerCutoff_le_self N hN sourceBeta sourceBeta_le) _

lemma inverse_power_base (n T k : ℕ) (hn : 0<n) (hnT : n≤T) (a D : ℝ) (ha : 0≤a)
    (hD : (T:ℝ)^k*(T:ℝ)^a≤D) : (n:ℝ)^k≤D*(n:ℝ)^(-a) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have h1 : (n:ℝ)^k*(n:ℝ)^a≤D := by
    apply le_trans _ hD
    exact mul_le_mul (pow_le_pow_left₀ hn0.le (by exact_mod_cast hnT) _)
      (Real.rpow_le_rpow hn0.le (by exact_mod_cast hnT) ha)
      (Real.rpow_nonneg hn0.le _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hh := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hn0.le (-a))
  rwa [mul_assoc,←Real.rpow_add hn0,add_neg_cancel,Real.rpow_zero,mul_one] at hh

end SquareDifference

end

end OAI
