import OAI.NumberTheory.TotientAsymptotic.LargestPrimeCofactor
import OAI.NumberTheory.TotientAsymptotic.CofactorSieveCutoff

namespace OAI

/-! Counting actual nonnormal primes with a sufficiently large final prime factor. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def normalityPrimeCutoff (x : ℝ) : ℝ := Real.exp (Real.log x/(100*B x))

def normalityLargeFactorPrimes (S : ℝ) (N : ℕ) : Finset ℕ :=
  (nonNormalPrimes S N).filter (fun p => normalityPrimeCutoff N ≤ largestPrimeFactor (p-1))

def normalityCofactors (S : ℝ) (N : ℕ) : Finset ℕ :=
  by
    classical
    exact (Finset.Icc 1 N).filter (fun b => (b:ℝ)*normalityPrimeCutoff N ≤ N ∧ AbnormalCofactor S N b)

lemma normality_large_factor_card {S : ℝ} (hS : 1 < S) (hBS : 0 ≤ B S) (N : ℕ) :
    (normalityLargeFactorPrimes S N).card ≤
      ∑ b ∈ normalityCofactors S N,(allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).card := by
  classical
  let Q := normalityCofactors S N
  let F := fun b => (allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).image (fun q => b*q+1)
  have hcover : normalityLargeFactorPrimes S N ⊆ Q.biUnion F := by
    intro p hp
    obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,hbad⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpN,hprime⟩ := Nat.mem_primesLE.mp hp
    obtain ⟨b,q,hb,hq,hqeq,hpeq,hbN,hco⟩ := nonnormal_largest_cofactor hS hBS hprime hpN hbad
    have hbR : (0:ℝ) < b := by exact_mod_cast hb
    have hprod : (b:ℝ)*q ≤ N := by exact_mod_cast (show b*q ≤ N by omega)
    have hqcut : normalityPrimeCutoff N ≤ q := by rwa [hqeq]
    have hbQ : b ∈ Q := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hb,hbN⟩,
        (mul_le_mul_of_nonneg_left hqcut hbR.le).trans hprod,hco⟩
    have hqX : q ≤ ⌊(N:ℝ)/b⌋₊ := by
      apply (Nat.le_floor_iff (div_nonneg (Nat.cast_nonneg N) hbR.le)).mpr
      exact (le_div_iff₀ hbR).mpr (by nlinarith)
    have hqF : q ∈ allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊ :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq.pos,hqX⟩,hq,by rwa [← hpeq]⟩
    exact Finset.mem_biUnion.mpr ⟨b,hbQ,Finset.mem_image.mpr ⟨q,hqF,hpeq.symm⟩⟩
  calc
    _ ≤ (Q.biUnion F).card := Finset.card_le_card hcover
    _ ≤ ∑ b ∈ Q,(F b).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun b _ => Finset.card_image_le)

 theorem normality_large_factor_count : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ,
    2 < S → 4 ≤ B S → ∀ N : ℕ, Real.exp 2 ≤ N → 1 ≤ B N →
    1 ≤ Real.log N/(200*B N) →
    ((normalityLargeFactorPrimes S N).card:ℝ) ≤
      C*N/Real.log N*(B N)^5*(Real.log S)^(-1/6:ℝ) := by
  classical
  obtain ⟨C,hC,hpair⟩ := cofactor_sieve_cutoff_mass
  obtain ⟨D,hD,hmass⟩ := abnormal_cofactor_mass
  refine ⟨C*D,by positivity,?_⟩
  intro S hS hBS N hN hBN hL
  let Q := normalityCofactors S N
  have hB : 0 < B N := by linarith
  have hNexp1 : Real.exp 1 ≤ (N:ℝ) := (Real.exp_le_exp.mpr (by norm_num)).trans hN
  have hlog : 0 < Real.log N := by
    have hx0 := (Real.exp_pos 2).trans_le hN
    have hh := (Real.le_log_iff_exp_le hx0).mpr hN
    linarith
  have hp := hpair N hN hB hL Q (by
    intro b hb
    obtain ⟨hb,hcut,_⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp hb).1,hcut⟩)
  have hm := hmass S hS hBS N hNexp1 hBN Q (by
    intro b hb
    obtain ⟨hb,_,hco⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp hb).1,(Finset.mem_Icc.mp hb).2,hco⟩)
  have hc : ((normalityLargeFactorPrimes S N).card:ℝ) ≤
      ∑ b ∈ Q,((allShiftedPrimePairs b ⌊(N:ℝ)/b⌋₊).card:ℝ) := by
    exact_mod_cast normality_large_factor_card (by linarith : 1 < S) (by linarith : 0 ≤ B S) N
  calc
    _ ≤ _ := hc.trans hp
    _ ≤ (C*N*(B N)^3/(Real.log N)^2)*(D*(B N)^2*Real.log N*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by field_simp

end TotientAsymptotic

end

end OAI
