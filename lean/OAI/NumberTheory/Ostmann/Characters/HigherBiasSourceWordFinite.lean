import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceWordDefs

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.HigherBiasSourceWord
open Construction Preliminaries

theorem sum_binMean {Q m : ℕ} (bulk top : FinitePrior (PrimeUpTo Q))
    {τ T : ℝ} (hbulk : ∀p,bulk.mass p≠0 → Real.log (p.val:ℝ)≤T)
    (htop : ∀p,top.mass p≠0 → τ≤Real.log (p.val:ℝ) ∧ Real.log (p.val:ℝ)≤Real.exp 1*τ)
    (hsmall : (m:ℝ)*T≤τ) (f : PrimeUpTo Q → ℤ → ℂ) (n : ℤ) :
    (∑J : ↥(bins τ),binMean bulk top m f J n) =
      (bulk.cmean (fun p=>f p n))^m * top.cmean (fun p=>f p n) := by
  classical
  have he : (∑J : ↥(bins τ),binMean bulk top m f J n)=
      (productPrior (rolePrior bulk top m)).cmean (fun w=>∏i,f (w i) n) := by
    unfold binMean FinitePrior.cmean
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [←Finset.mul_sum]
    by_cases hw : (productPrior (rolePrior bulk top m)).mass w=0
    · simp only [hw,Complex.ofReal_zero,zero_mul]
    · congr 1
      have hm := floor_wordLog_mem_bins bulk top hbulk htop hsmall w hw
      rw [Finset.sum_eq_single (⟨⌊wordLog w⌋,hm⟩ : ↥(bins τ))]
      · simp only [ite_true]
      · intro J _ hJ
        have hn : ⌊wordLog w⌋≠(J:ℤ) := by
          intro h
          apply hJ
          exact Subtype.ext h.symm
        simp only [hn,ite_false]
      · simp
  rw [he,productPrior_cmean (rolePrior bulk top m) (fun _ p=>f p n),Fin.prod_univ_add]
  simp only [rolePrior,Fin.append_left,Fin.append_right,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_one]

theorem common_bin {Q m : ℕ} (bulk top : FinitePrior (PrimeUpTo Q))
    {τ T δ : ℝ} (hτ : 0≤τ) (hδ : 0≤δ)
    (hbulk : ∀p,bulk.mass p≠0 → Real.log (p.val:ℝ)≤T)
    (htop : ∀p,top.mass p≠0 → τ≤Real.log (p.val:ℝ) ∧ Real.log (p.val:ℝ)≤Real.exp 1*τ)
    (hsmall : (m:ℝ)*T≤τ) (f : PrimeUpTo Q → ℤ → ℂ) (H : Finset ℤ)
    (hmean : ∀n∈H,δ≤(bulk.cmean (fun p=>f p n)).re ∧
      δ≤(top.cmean (fun p=>f p n)).re) :
    ∃J∈bins τ,∃H₀ : Finset ℤ,H₀⊆H ∧ H.card≤(bins τ).card*H₀.card ∧
      ∀n∈H₀,δ^(m+1)≤((bins τ).card:ℝ)*‖binMean bulk top m f J n‖ := by
  classical
  have ht : τ≤(Real.exp 1+1)*τ := by nlinarith [Real.exp_pos (1:ℝ)]
  have : Nonempty ↥(bins τ) := ⟨⟨⌊τ⌋,Finset.mem_Icc.mpr
    ⟨le_rfl,Int.floor_mono ht⟩⟩⟩
  have hlarge : ∀n∈H,δ^(m+1)≤‖∑J : ↥(bins τ),binMean bulk top m f J n‖ := by
    intro n hn
    rw [sum_binMean bulk top hbulk htop hsmall,norm_mul,norm_pow,pow_succ]
    exact mul_le_mul
      (pow_le_pow_left₀ hδ ((hmean n hn).1.trans (Complex.re_le_norm _)) m)
      ((hmean n hn).2.trans (Complex.re_le_norm _)) hδ (by positivity)
  obtain ⟨J,hJ⟩ := common_bin_many_endpoints H
    (fun n (J : ↥(bins τ))=>binMean bulk top m f J n) (δ^(m+1)) hlarge
  refine ⟨J,J.property,H.filter (fun n=>δ^(m+1)≤
    (Fintype.card ↥(bins τ):ℝ)*‖binMean bulk top m f J n‖),
    Finset.filter_subset _ _,?_,?_⟩
  · simpa only [Fintype.card_coe] using hJ
  · intro n hn
    simpa only [Fintype.card_coe] using (Finset.mem_filter.mp hn).2

end Ostmann.Characters.HigherBiasSourceWord

end

end OAI
