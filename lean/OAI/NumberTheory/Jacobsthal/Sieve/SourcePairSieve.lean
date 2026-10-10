import OAI.NumberTheory.Jacobsthal.Estimates.SourcePairRemainder

namespace OAI

namespace Erdos970


namespace ErdosVarianceLargeCount
open NumberTheoryLean ErdosHyperbolaError
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

noncomputable def siftedSourcePairs (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ)
    (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) (P : Finset ℕ) : Finset (ℤ × ℤ) :=
  (sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ).filter
    (fun pm => ∀ t ∈ P,¬(t : ℤ) ∣ pm.1)

theorem siftedSourcePairs_sum (H T0 T1 : ℕ) (C0 k0 p0 p1 m1 : ℤ)
    (x0 x1 y0 y1 : ℝ) (lcI rcI lcJ rcJ : Bool) (P : Finset ℕ) :
    ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ P).card : ℝ) =
      ∑ pm ∈ sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ,
        (1 : ℝ)*BonferroniBlocks.survives P (fun t => (t : ℤ) ∣ pm.1) := by
  rw [siftedSourcePairs,Finset.card_filter,Nat.cast_sum]
  simp only [Nat.cast_ite,Nat.cast_one,Nat.cast_zero,one_mul,BonferroniBlocks.survives]
  apply Finset.sum_congr rfl
  intro pm _hpm
  split_ifs <;> rfl

theorem source_pair_sieve_upper (H T0 T1 : ℕ) (hH : 2 ≤ H) (hT0 : 0 < T0) (hT1 : 0 < T1)
    (hSF : Squarefree T0) (hsupport : ∀ t : ℕ,t.Prime → t ∣ T0 → t ∣ H)
    (hT1N : T1.Coprime (H*T0)) (C0 k0 p0 p1 m1 : ℤ)
    (hC0 : Int.gcd C0 (H : ℤ) = 1) (hp0 : Int.gcd p0 (T0 : ℤ) = 1)
    (hp1 : Int.gcd p1 (T1 : ℤ) = 1) (P : Finset ℕ) (hP : ∀ t ∈ P,t.Prime)
    (hPcop : ∀ t ∈ P,t.Coprime (H*T1)) (v s : ℝ) (hv : 2 ≤ v) (hs : 480024 ≤ s)
    (hPv : ∀ t ∈ P,(t : ℝ) ≤ v)
    (x0 x1 y0 y1 : ℝ) (hx : x0 ≤ x1) (hy : y0 ≤ y1) (lcI rcI lcJ rcJ : Bool) :
    ((siftedSourcePairs H T0 T1 C0 k0 p0 p1 m1 x0 x1 y0 y1 lcI rcI lcJ rcJ P).card : ℝ) ≤
      sourceMain H T0 T1 (x1-x0) (y1-y0)*(∏ t ∈ P,(1-1/(t : ℝ)))*(1+Real.exp (-s/96))+
      ∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
        hyperbolaEnvelope H T0*(1+(x1-x0)/((d : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ)) := by
  let C := sourcePairs H T0 T1 C0 k0 p0 p1 m1 1 x0 x1 y0 y1 lcI rcI lcJ rcJ
  let X := sourceMain H T0 T1 (x1-x0) (y1-y0)
  have hX : 0 ≤ X := by dsimp [X,sourceMain];positivity
  have hf := RealFundamentalSieve.fundamental_lemma C (fun _ => 1) (fun _ _ => by norm_num)
    (fun t pm => (t : ℤ) ∣ pm.1) v s P X (fun t => 1/(t : ℝ)) hv hs hX hP hPv
    (fun _ _ => by positivity) (fun t _ => div_le_div_of_nonneg_right (by norm_num) (Nat.cast_nonneg t))
    (fun _ => by norm_num)
  have hsq := IntervalBoundingSieve.squarefree_primeSet_product P hP
  have hprodCop : (∏ t ∈ P,t).Coprime (H*T1) := Nat.coprime_prod_left_iff.mpr hPcop
  have hrem : (∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
      |FundamentalBlockEstimate.integerRemainder C (fun _ => 1) (fun t pm => (t : ℤ) ∣ pm.1) X
        (fun t => 1/(t : ℝ)) d|) ≤
      ∑ d ∈ RealFundamentalSieve.levelDivisors P v s,
        hyperbolaEnvelope H T0*(1+(x1-x0)/((d : ℝ)*((H*T0 : ℕ) : ℝ))+(y1-y0)/((H*T0 : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro d hd
    have hdiv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact source_pair_remainder_bound H T0 T1 hH hT0 hT1 hSF hsupport hT1N C0 k0 p0 p1 m1
      hC0 hp0 hp1 d (hsq.squarefree_of_dvd hdiv) (hprodCop.of_dvd_left hdiv)
      x0 x1 y0 y1 hx hy lcI rcI lcJ rcJ
  rw [siftedSourcePairs_sum]
  have hu := (abs_le.mp hf).2
  dsimp [C,X] at *
  nlinarith

end ErdosVarianceLargeCount


end Erdos970

end OAI
