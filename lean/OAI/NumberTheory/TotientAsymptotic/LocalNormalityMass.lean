import OAI.NumberTheory.TotientAsymptotic.CandidateNormalMass
import OAI.NumberTheory.TotientAsymptotic.LocalNormalityDecay

namespace OAI

/-! Ford's proved exceptional-prime estimate at each local indexed scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

lemma localNormalityScale_gt_two (h : ℕ) : 2 < localNormalityScale h := by
  have he := Real.one_le_exp (show 0 ≤ (h:ℝ)^4 by positivity)
  have htwo : 2 < Real.exp 1 := by
    linarith only [Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)]
  exact htwo.trans_le (Real.exp_le_exp.mpr he)

theorem local_non_normal_prime_mass : ∃ C : ℝ,0 < C ∧ ∀ h : ℕ,∀ b : ℝ,2 ≤ b →
    (∑ p ∈ nonNormalPrimes (localNormalityScale h) (discardPrimeBound b),
      ((p-1:ℕ):ℝ)⁻¹) ≤ C*(2*b+2)^6*Real.exp (-(h:ℝ)^4/6) := by
  obtain ⟨C,hC,hbound⟩ := non_normal_prime_mass fordLemma26Input
  refine ⟨C,hC,?_⟩
  intro h b hb
  have hs : 0 ≤ (h:ℝ)^4 := by positivity
  have hS := localNormalityScale_gt_two h
  have hBS : 0 ≤ B (localNormalityScale h) := by
    simpa only [localNormalityScale,B,Real.log_exp] using hs
  obtain ⟨hN,hBN,hBU,_⟩ := discardPrimeBound_bounds hb
  have hM := discardExponent_bounds hb
  have he := hbound _ hS hBS _ hN
  rw [show Nat.clog 2 (discardPrimeBound b)=discardExponent b from
    Nat.clog_pow 2 _ (by norm_num)] at he
  rw [localNormalityScale_factor] at he
  have hBpow : (B ((2:ℝ)^discardExponent b))^5 ≤ (2*b+2)^5 := by
    apply pow_le_pow_left₀
    · simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBN
    · exact (show B ((2:ℝ)^discardExponent b) ≤ 2*b+1 by
        simpa only [discardPrimeBound,Nat.cast_pow,Nat.cast_ofNat] using hBU).trans
          (by linarith)
  calc
    _ ≤ C*(B ((2:ℝ)^discardExponent b))^5*(1+Real.log (discardExponent b))*
        Real.exp (-(h:ℝ)^4/6) := he
    _ ≤ C*(2*b+2)^5*(2*b+2)*Real.exp (-(h:ℝ)^4/6) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      apply mul_le_mul (mul_le_mul_of_nonneg_left hBpow hC.le) (by linarith only [hM.2])
      · have hm2 : (1:ℝ) ≤ discardExponent b := by
          exact_mod_cast (show 1 ≤ discardExponent b by omega)
        linarith only [Real.log_nonneg hm2]
      · positivity
    _ = _ := by ring


end TotientAsymptotic

end

end OAI
