import OAI.NumberTheory.TotientAsymptotic.PrimeDiscardCutoff
import OAI.NumberTheory.TotientAsymptotic.NormalityInput
import OAI.NumberTheory.TotientAsymptotic.MertensProduct
import OAI.NumberTheory.TotientAsymptotic.ExceptionalPrimeMass

namespace OAI

/-! The normality prime-mass saving at the full-fiber construction's cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

def candidateNormalityScale (b : ℝ) : ℝ := Real.exp (Real.exp ((Real.log b)^10))

lemma candidateNormalityScale_gt_two (b : ℝ) : 2 < candidateNormalityScale b := by
  have he := Real.one_le_exp (show 0 ≤ (Real.log b)^10 by positivity)
  have htwo : 2 < Real.exp 1 := by
    linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
  exact htwo.trans_le (Real.exp_le_exp.mpr he)

lemma candidateNormalityScale_factor (b : ℝ) :
    (Real.log (candidateNormalityScale b))^(-1/6:ℝ)=
      Real.exp (-((Real.log b)^10)/6) := by
  rw [candidateNormalityScale,Real.log_exp,←Real.exp_mul]
  congr 1
  ring

theorem candidate_non_normal_mass : ∃ C : ℝ,0 < C ∧ ∀ b : ℝ,2 ≤ b →
    (∑ p ∈ nonNormalPrimes (candidateNormalityScale b) (discardPrimeBound b),
      ((p-1:ℕ):ℝ)⁻¹) ≤ C*(2*b+2)^6*Real.exp (-((Real.log b)^10)/6) := by
  obtain ⟨C,hC,hbound⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨C,hC,?_⟩
  intro b hb
  have hs : 0 ≤ (Real.log b)^10 := by positivity
  have hS := candidateNormalityScale_gt_two b
  have hBS : 0 ≤ B (candidateNormalityScale b) := by
    simpa only [candidateNormalityScale,B,Real.log_exp] using hs
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  have hM := discardExponent_bounds hb
  have he := hbound _ hS hBS _ hN
  rw [show Nat.clog 2 (discardPrimeBound b)=discardExponent b from
    Nat.clog_pow 2 _ (by norm_num)] at he
  rw [candidateNormalityScale_factor] at he
  have hBpow : (B ((2:ℝ)^discardExponent b))^5 ≤ (2*b+2)^5 := by
    apply pow_le_pow_left₀
    · simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBN
    · exact (show B ((2:ℝ)^discardExponent b) ≤ 2*b+1 by
        simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBU).trans
          (by linarith)
  calc
    _ ≤ C*(B ((2:ℝ)^discardExponent b))^5*(1+Real.log (discardExponent b))*
        Real.exp (-((Real.log b)^10)/6) := he
    _ ≤ C*(2*b+2)^5*(2*b+2)*Real.exp (-((Real.log b)^10)/6) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul (mul_le_mul_of_nonneg_left hBpow hC.le) (by linarith only [hM.2])
      · have hm2 : (1:ℝ) ≤ discardExponent b := by
          exact_mod_cast (show 1 ≤ discardExponent b by omega)
        linarith only [Real.log_nonneg hm2]
      · positivity
    _ = _ := by ring

lemma candidate_total_prime_mass : ∃ D : ℝ,0 < D ∧ ∀ b : ℝ,2 ≤ b →
    (∑ p ∈ Nat.primesLE (discardPrimeBound b),((p-1:ℕ):ℝ)⁻¹) ≤ D*(2*b+2) := by
  obtain ⟨D,hD,hbound⟩ := prime_reciprocal_mass_bound mertensProductInput
  refine ⟨D,hD,?_⟩
  intro b hb
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  apply (hbound _ (by omega) hBN).trans
  exact mul_le_mul_of_nonneg_left (by linarith only [hBU]) hD.le

lemma candidate_prime_cutoff : ∀ᶠ x : ℝ in atTop,x ≤ discardPrimeBound (B x) := by
  filter_upwards [B_tendsto.eventually (eventually_ge_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with x hB hx
  have hl := (discardPrimeBound_bounds hB).2.2.2
  calc
    x = Real.exp (Real.exp (B x)) := by
      simp only [B,Real.exp_log (Real.log_pos hx),Real.exp_log (zero_lt_one.trans hx)]
    _ ≤ Real.exp (Real.exp ((6/5:ℝ)*B x)) :=
      Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hB]))
    _ ≤ _ := hl

end TotientAsymptotic

end

end OAI
