import OAI.NumberTheory.Ostmann.Construction.FiniteProductBins
import OAI.NumberTheory.Ostmann.Construction.HarmonicPriorEvent

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

abbrev PrimeGroupSample (S : PrimeSource) (b : ℕ) := Fin b → S.Sample

def primeGroupPrior (S : PrimeSource) (b : ℕ) : FinitePrior (PrimeGroupSample S b) :=
  dependentProductPrior (fun _ : Fin b => S.law)

def primeGroupLog (S : PrimeSource) (b : ℕ) (x : PrimeGroupSample S b) : ℝ :=
  ∑ i, Real.log (x i : ℕ)

def primeGroupBalanced (d : Decomposition) (S : PrimeSource) (b : ℕ)
    (x : PrimeGroupSample S b) : ℝ := ∏ i, balancedPrimeIndicator d (x i)

def primeGroupBinMass (d : Decomposition) (S : PrimeSource) (b : ℕ) (t : ℤ) : ℝ :=
  (primeGroupPrior S b).mean (fun x =>
    Ostmann.smoothPartition (primeGroupLog S b x-t)*primeGroupBalanced d S b x)

theorem primeGroupBalanced_mean_lower (d : Decomposition) (S : PrimeSource) (b : ℕ)
    (hS : (1/2:ℝ) ≤ S.law.mean (fun p => balancedPrimeIndicator d p)) :
    (1/2:ℝ)^b ≤ (primeGroupPrior S b).mean (primeGroupBalanced d S b) := by
  change (1/2:ℝ)^b ≤ (dependentProductPrior (fun _ : Fin b => S.law)).mean
    (fun x => ∏ i, balancedPrimeIndicator d (x i))
  simpa only [Fintype.card_fin] using
    dependentProductPrior_mean_lower (fun _ : Fin b => S.law)
      (fun _ p => balancedPrimeIndicator d p) (by norm_num : (0:ℝ) ≤ 1/2)
      (fun _ => hS)

theorem primeGroupLog_bounds (S : PrimeSource) (b : ℕ) (lo hi : ℝ)
    (hS : ∀ p : S.Sample, lo ≤ Real.log (p:ℕ) ∧ Real.log (p:ℕ) ≤ hi)
    (x : PrimeGroupSample S b) :
    (b:ℝ)*lo ≤ primeGroupLog S b x ∧ primeGroupLog S b x ≤ (b:ℝ)*hi := by
  change (b:ℝ)*lo ≤ (∑ i, Real.log (x i : ℕ)) ∧
    (∑ i, Real.log (x i : ℕ)) ≤ (b:ℝ)*hi
  constructor
  · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hS (x i)).1))
  · simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using (Finset.sum_le_sum (s := Finset.univ) (fun i _ => (hS (x i)).2))

theorem exists_primeGroup_bin (d : Decomposition) (S : PrimeSource) (b : ℕ)
    (lo hi : ℝ) (hlo : lo ≤ hi)
    (hS : ∀ p : S.Sample, lo ≤ Real.log (p:ℕ) ∧ Real.log (p:ℕ) ≤ hi)
    (hbal : (1/2:ℝ) ≤ S.law.mean (fun p => balancedPrimeIndicator d p)) :
    ∃ t : ℤ, (b:ℝ)*lo-2 < (t:ℝ) ∧ (t:ℝ) < (b:ℝ)*hi+2 ∧
      (1/2:ℝ)^b/(2*((b:ℝ)*(hi-lo)+5)) < primeGroupBinMass d S b t := by
  have hmean := primeGroupBalanced_mean_lower d S b hbal
  have hmean0 : 0 < (primeGroupPrior S b).mean (primeGroupBalanced d S b) :=
    lt_of_lt_of_le (by positivity) hmean
  obtain ⟨t,ht,hpos⟩ := exists_finitePrior_logCell (primeGroupPrior S b)
    (primeGroupLog S b) (primeGroupBalanced d S b) ((b:ℝ)*lo) ((b:ℝ)*hi)
    (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg b))
    (primeGroupLog_bounds S b lo hi hS) hmean0
  obtain ⟨htlo,hthi⟩ := logBlockCenters_bounds ((b:ℝ)*lo)
    ((b:ℝ)*hi-(b:ℝ)*lo) ht
  refine ⟨t,htlo,by linarith,?_⟩
  have hd : 0 ≤ 2*((b:ℝ)*hi-(b:ℝ)*lo+5) := by
    have := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg b)
    linarith
  have hdiv := div_le_div_of_nonneg_right hmean hd
  have he : (b:ℝ)*hi-(b:ℝ)*lo=(b:ℝ)*(hi-lo) := by ring
  rw [he] at hpos hdiv
  exact hdiv.trans_lt hpos

theorem harmonicBand_log_support {α β L : ℝ} {E : Finset ℕ}
    (hZ : 0 < harmonicPrimeMass (logLogPrimeBand (α*L) (β*L) \ E))
    (p : (harmonicPrimeSource (logLogPrimeBand (α*L) (β*L) \ E)
      (fun _q hq => logLogPrimeBand_prime (Finset.mem_sdiff.mp hq).1) hZ).Sample) :
    Real.exp (α*L) ≤ Real.log (p:ℕ) ∧ Real.log (p:ℕ) ≤ Real.exp (β*L) := by
  have hp := (logLogPrimeBand_mem_iff (α*L) (β*L) (p:ℕ)).mp
    (Finset.mem_sdiff.mp p.property).1
  have hl : 0 < Real.log (p:ℕ) := Real.log_pos (by exact_mod_cast hp.1.one_lt)
  constructor
  · exact (Real.exp_le_exp.mpr hp.2.1.le).trans_eq (Real.exp_log hl)
  · simpa only [Real.exp_log hl] using Real.exp_le_exp.mpr hp.2.2

end Ostmann.Construction

end

end OAI
