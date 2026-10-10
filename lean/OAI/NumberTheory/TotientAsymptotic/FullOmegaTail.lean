import OAI.NumberTheory.TotientAsymptotic.FullOmegaMoment
import OAI.NumberTheory.TotientAsymptotic.SmallFactorTail
import OAI.NumberTheory.TotientAsymptotic.SmoothCountingSplit

namespace OAI

/-! The large-normality-parameter range from the full factor-count moment. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma full_factor_tail_weight {S : ℝ} {n : ℕ} (hn : 0 < n)
    (hbad : 2*B S ≤ (n.primeFactorsList.length:ℝ)) :
    (n:ℝ)⁻¹ ≤ Real.exp (-2*B S*Real.log (3/2:ℝ))*omegaReciprocal n := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (3/2:ℝ) := Real.log_pos (by norm_num)
  have he : 1 ≤ Real.exp (-2*B S*Real.log (3/2:ℝ))*(3/2:ℝ)^n.primeFactorsList.length := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 3/2),← Real.exp_add]
    apply Real.one_le_exp
    nlinarith
  have hh := mul_le_mul_of_nonneg_right he (inv_nonneg.mpr hnR.le)
  simpa only [omegaReciprocal,MonoidHom.coe_mk,OneHom.coe_mk,one_mul,div_eq_mul_inv,
    mul_assoc] using hh

lemma full_factor_tail_mass : ∃ C : ℝ, 0 < C ∧ ∀ S : ℝ, 1 < S → ∀ N : ℕ,
    2 ≤ N → 0 ≤ B N → 6*B N ≤ B S → ∀ Q : Finset ℕ,
    (∀ n ∈ Q,0 < n ∧ n ≤ N ∧ 2*B S ≤ (n.primeFactorsList.length:ℝ)) →
    (Q.card:ℝ) ≤ C*N/Real.log N*(Real.log S)^(-1/6:ℝ) := by
  obtain ⟨C,hC,hmoment⟩ := full_omega_moment_bound
  refine ⟨C,hC,?_⟩
  intro S hS N hN hBN hBS Q hQ
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogS : 0 < Real.log S := Real.log_pos hS
  have hm := hmoment N hN Q (fun n hn => ⟨(hQ n hn).1,(hQ n hn).2.1⟩)
  have hrec : (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (-2*B S*Real.log (3/2:ℝ))*(∑ n ∈ Q,omegaReciprocal n) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun n hn => full_factor_tail_weight (hQ n hn).1 (hQ n hn).2.2)
  have hexp : Real.exp (-2*B S*Real.log (3/2:ℝ))*(Real.log N)^(3/2:ℝ) ≤
      (Real.log N)⁻¹*(Real.log S)^(-1/6:ℝ) := by
    have hinv : (Real.log N)⁻¹ = Real.exp (-B N) := by
      rw [Real.exp_neg,B,Real.exp_log hlog]
    rw [Real.rpow_def_of_pos hlog,Real.rpow_def_of_pos hlogS,
      hinv,← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold B at *
    have hs : 0 ≤ Real.log (Real.log S) := by linarith
    nlinarith [log_three_halves_lower]
  have hcard := card_le_endpoint_reciprocal Q N (fun n hn =>
    ⟨(hQ n hn).1,by exact_mod_cast (hQ n hn).2.1⟩)
  calc
    _ ≤ N*(Real.exp (-2*B S*Real.log (3/2:ℝ))*(C*(Real.log N)^(3/2:ℝ))) :=
      hcard.trans (mul_le_mul_of_nonneg_left (hrec.trans
        (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le)) (Nat.cast_nonneg N))
    _ = C*N*(Real.exp (-2*B S*Real.log (3/2:ℝ))*(Real.log N)^(3/2:ℝ)) := by ring
    _ ≤ C*N*((Real.log N)⁻¹*(Real.log S)^(-1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end TotientAsymptotic

end

end OAI
