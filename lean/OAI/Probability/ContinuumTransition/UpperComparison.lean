import OAI.Probability.ContinuumTransition.AppendAttraction

namespace OAI

section
open scoped BigOperators
open MeasureTheory Set
namespace ContinuumTemperature

theorem physical_kac_log_upper {C : NNReal} (hC : LipschitzWith C kernel)
    {t β a S : ℝ} (ht : 0 < t) (hβ : 0 < β) (ha : 0 ≤ a) (hS : 1 ≤ S)
    {σ R : ℕ → ℝ} (hσ : ∀ n, 0 ≤ σ n) (hR : ∀ n, 1 ≤ R n) (hs : Summable σ)
    (hsmall : 2197*t*kernelHeight*(a+∑' n, σ n) ≤ (t^2/8)/8)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) (hbound : ∀ n, σ n ≠ 0 → R n ≤ R₀)
    {q : ℕ} (hq : 0 < q)
    (hcoeff : β*(t*a)*(1+kacRowError C S ((q : ℝ)/4))/2 ≤
      β*(t^2/8-2197*t*kernelHeight*(∑' n, σ n)/2)/(4+2/((q : ℝ)/4))^3) (m : ℕ) (h : ℝ) :
    Real.log (grandPartition (physicalProfile t (prepend a σ) (prepend S R)) t β h ((m : ℝ)*(q : ℝ)/2)) ≤
      (gridIndices m 1).card*Real.log (∑' n, quadraticGrandTerm (physicalProfile t σ R) β (t*h)
        (β*(t*a)*(1+kacRowError C S ((q : ℝ)/4))/2) ((q : ℝ)/4) n)+
      β*(momentConstant t β (t*h)/2)*(boundaryIndices m q (cellRadius R₀).toNat).card*
        (2197*t*kernelHeight*(∑' n, σ n)) := by
  have hσ' := prepend_nonneg (le_refl 0) hσ
  have hτ' := prepend_nonneg ha (fun _ => le_refl (0 : ℝ))
  have hR' := prepend_ge_one hS hR
  have hs' := summable_prepend 0 hs
  have hτs' := summable_prepend a summable_zero
  have he : (fun n => prepend 0 σ n+prepend a (fun _ => 0) n) = prepend a σ := by
    funext n; cases n <;> simp
  have hsmall' : 2197*t*kernelHeight*(∑' n, (prepend 0 σ n+prepend a (fun _ => 0) n)) ≤ (t^2/8)/8 := by
    rw [he, tsum_prepend a hs]; exact hsmall
  have hb' (n : ℕ) (hn : prepend 0 σ n ≠ 0) : prepend S R n ≤ R₀ := by
    cases n with
    | zero => exact False.elim (hn rfl)
    | succ n => exact hbound n hn
  have hh := physical_log_cut_bound ht hβ hσ' hτ' hR' hs' hτs' hsmall' hR₀ hb' m q hq h
  have hcut : cutReference t (prepend 0 σ) (prepend a (fun _ => 0)) (prepend S R) q =
      cutKac q (physicalProfile t σ R) (t*a) S := by
    funext x y
    exact cutReference_prepend t a S hσ hR hs q x y
  rw [he, hcut, tsum_prepend 0 hs, zero_add] at hh
  have hc0 : 0 ≤ 2197*t*kernelHeight := mul_nonneg (mul_nonneg (by norm_num) ht.le) kernelHeight_pos.le
  have hsub := mul_le_mul_of_nonneg_left (show (∑' n, σ n) ≤ a+∑' n, σ n by linarith) hc0
  have hsm : 2197*t*kernelHeight*(∑' n, σ n)/2 ≤ t^2/8 := by
    nlinarith only [hsmall, hsub, sq_nonneg t]
  have hG := kac_cut_grand_le hC ht.le hβ.le (mul_nonneg ht.le ha) (lt_of_lt_of_le zero_lt_one hS)
    hσ hR hs hsm hq hcoeff m (μ := t*h)
  have hF := cellLowerBound_gibbs_finite ht.le hβ.le
    (fun n => add_nonneg (hσ' n) (hτ' n)) hR' (hs'.add hτs') hsmall'
    ((deletedCore_lower ht.le hσ' hτ' hR' hs' hτs' q).mono
      (deletedCore_le_cutReference (τ := prepend a (fun _ => 0)) ht.le hσ' hR' q))
    (measurable_cutReference t hσ' hτ' hR' hs' hτs' q)
    (show volume (cube ((m : ℝ)*(q : ℝ)/2)) ≠ ⊤ by
      rw [volume_cube]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (t*h)
  rw [hcut] at hF
  have hp := grandIntegral_gibbs_pos (cutKac q (physicalProfile t σ R) (t*a) S) β (t*h) _ hF.summable
  have hl := Real.log_le_log hp hG
  rw [Real.log_pow] at hl
  exact hh.trans (add_le_add hl (le_refl _))

end ContinuumTemperature
end

end OAI
