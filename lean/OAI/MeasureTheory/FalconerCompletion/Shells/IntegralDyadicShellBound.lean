import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Fourier.LintegralBiUnionFinsetLe

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
namespace CriticalFourierSupport
namespace CurrentFalconer
open MeasureTheory Set
open scoped ENNReal

theorem integral_dyadic_shell_bound (f : ℝ → ℝ) (hf : Continuous f)
    (hnonneg : ∀ s, 0 ≤ f s) {H A : ℝ} (hH : 1 ≤ H) (hA : 0 ≤ A)
    (hlow : (∫ s : ℝ in Set.Icc (-1) 1, f s) ≤ 2)
    (hshell : ∀ B : ℝ, 1 ≤ B → B ≤ H →
      (∫ s : ℝ in annularScalarSet B H, f s) ≤ A) :
    (∫ s : ℝ in Set.Icc (-H) H, f s) ≤
      2 + (Real.log H / Real.log 2 + 1) * A := by
  obtain ⟨n, hn, hHn⟩ := exists_nat_pow_near hH (by norm_num : (1 : ℝ) < 2)
  have hi : IntegrableOn f (Set.Icc (-H) H) := hf.integrableOn_Icc
  have hi0 : IntegrableOn f (Set.Icc (-1) 1) := hf.integrableOn_Icc
  have hishell (B : ℝ) : IntegrableOn f (annularScalarSet B H) := by
    apply hi.mono_set
    intro s hs
    exact abs_le.mp (hs.2.trans (min_le_right _ _))
  have hsh (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫⁻ s : ℝ in annularScalarSet ((2 : ℝ)^j) H, ENNReal.ofReal (f s)) ≤
        ENNReal.ofReal A := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hishell _) (ae_of_all _ hnonneg)]
    apply ENNReal.ofReal_le_ofReal (hshell _ (one_le_pow₀ (by norm_num)) _)
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans hn
  have hlow' : (∫⁻ s : ℝ in Set.Icc (-1) 1, ENNReal.ofReal (f s)) ≤
      ENNReal.ofReal 2 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hi0 (ae_of_all _ hnonneg)]
    exact ENNReal.ofReal_le_ofReal hlow
  have hsum : (∑ _j ∈ Finset.range (n+1), ENNReal.ofReal A) =
      ENNReal.ofReal (((n : ℝ)+1)*A) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hA)]
    simp
  have hbound : ENNReal.ofReal (∫ s : ℝ in Set.Icc (-H) H, f s) ≤
      ENNReal.ofReal (2+((n : ℝ)+1)*A) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hnonneg)]
    calc
      _ ≤ ∫⁻ s : ℝ in Set.Icc (-1) 1 ∪
          ⋃ j ∈ Finset.range (n+1), annularScalarSet ((2 : ℝ)^j) H,
          ENNReal.ofReal (f s) := lintegral_mono_set (dyadic_scalar_cover hHn)
      _ ≤ (∫⁻ s : ℝ in Set.Icc (-1) 1, ENNReal.ofReal (f s)) +
          ∫⁻ s : ℝ in ⋃ j ∈ Finset.range (n+1), annularScalarSet ((2 : ℝ)^j) H,
            ENNReal.ofReal (f s) := lintegral_union_le _ _ _
      _ ≤ ENNReal.ofReal 2 + ∑ j ∈ Finset.range (n+1),
          ∫⁻ s : ℝ in annularScalarSet ((2 : ℝ)^j) H, ENNReal.ofReal (f s) :=
        add_le_add hlow' (lintegral_biUnion_finset_le _ _ _ _)
      _ ≤ ENNReal.ofReal 2 + ∑ _j ∈ Finset.range (n+1), ENNReal.ofReal A :=
        add_le_add le_rfl (Finset.sum_le_sum hsh)
      _ = _ := by
        rw [hsum, ← ENNReal.ofReal_add (by norm_num) (by positivity)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnlog : (n : ℝ) ≤ Real.log H / Real.log 2 := by
    apply (le_div_iff₀ hlog2).mpr
    have h := Real.log_le_log (by positivity) hn
    simpa only [Real.log_pow] using h
  apply ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by linarith :
    (n : ℝ)+1 ≤ Real.log H / Real.log 2 + 1) hA)

end CurrentFalconer
end CriticalFourierSupport
end
end

end OAI
