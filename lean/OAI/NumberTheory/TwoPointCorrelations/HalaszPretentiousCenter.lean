import OAI.NumberTheory.TwoPointCorrelations.HalaszGeneralTwist
import OAI.NumberTheory.TwoPointCorrelations.MRTCountMean
import Mathlib.Topology.Order.Compact

namespace OAI

/-! The minimizing twist and the elementary part of MRT Lemma A.4(ii).
Two nearby candidates for the minimum force a lower bound by an explicit
prime cosine sum. Analytic estimates for that prime sum are kept separate. -/

namespace TwoPointCorrelations

open Finset
open scoped ComplexConjugate

lemma halasz_distance_continuous (F : ℕ → ℂ) (N : ℕ) :
    Continuous (fun t : ℝ => squaredDistance F (mrtArchimedeanTwist t) N) := by
  unfold squaredDistance mrtArchimedeanTwist
  fun_prop

theorem halasz_minimizing_twist (F : ℕ → ℂ) (N : ℕ) :
    ∃ t₁ : ℝ, |t₁| ≤ (N : ℝ) ∧ ∀ t : ℝ, |t| ≤ (N : ℝ) →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  have hn : -(N : ℝ) ≤ N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hn) (halasz_distance_continuous F N).continuousOn
  refine ⟨t₁, abs_le.mpr ht₁, fun t ht => hmin (abs_le.mp ht)⟩

lemma halasz_twist_sum_norm (t s : ℝ) (n : ℕ) :
    ‖mrtArchimedeanTwist t n + mrtArchimedeanTwist s n‖ =
      2 * |Real.cos ((t - s) * Real.log (n : ℝ) / 2)| := by
  let u := (t + s) / 2
  let v := (t - s) * Real.log (n : ℝ) / 2
  have he : mrtArchimedeanTwist t n + mrtArchimedeanTwist s n =
      mrtArchimedeanTwist u n * ((2 : ℂ) * (Real.cos v : ℂ)) := by
    rw [Complex.ofReal_cos, Complex.two_cos, mul_add]
    unfold mrtArchimedeanTwist
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1 <;> congr 1 <;> dsimp [u, v] <;> push_cast <;> ring
  rw [he, norm_mul, mrtArchimedeanTwist_norm, one_mul, norm_mul,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]

theorem halasz_two_twist_distance (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (t s : ℝ) :
    2 * (∑ p ∈ primesUpTo N,
      (1 - |Real.cos ((t - s) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
      squaredDistance F (mrtArchimedeanTwist t) N +
        squaredDistance F (mrtArchimedeanTwist s) N := by
  unfold squaredDistance
  rw [mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro p hp
  rw [← add_div, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg p)
  have hp0 := (mem_filter.mp hp).2.pos
  have hre : (F p * conj (mrtArchimedeanTwist t p)).re +
      (F p * conj (mrtArchimedeanTwist s p)).re ≤
        ‖mrtArchimedeanTwist t p + mrtArchimedeanTwist s p‖ := by
    calc
      _ = (F p * conj (mrtArchimedeanTwist t p + mrtArchimedeanTwist s p)).re := by
        simp only [map_add, mul_add, Complex.add_re]
      _ ≤ ‖F p * conj (mrtArchimedeanTwist t p + mrtArchimedeanTwist s p)‖ :=
        Complex.re_le_norm _
      _ = ‖F p‖ * ‖mrtArchimedeanTwist t p + mrtArchimedeanTwist s p‖ := by
        rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) (hF p hp0)
  rw [halasz_twist_sum_norm] at hre
  linarith

lemma halasz_distance_from_minimizer (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ primesUpTo N,
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  have h := halasz_two_twist_distance F hF N t t₁
  linarith

lemma halasz_prime_cosine_tail_lower (F : ℕ → ℂ) (hF : OneBounded F)
    (N : ℕ) (Y t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        squaredDistance F (mrtArchimedeanTwist t) N := by
  apply le_trans _ (halasz_distance_from_minimizer F hF N t t₁ hmin)
  apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
  intro p _ _
  exact div_nonneg (sub_nonneg.mpr (Real.abs_cos_le_one _)) (Nat.cast_nonneg p)

lemma halasz_masked_cosine_tail_lower (F : ℕ → ℂ) (hF : OneBounded F)
    (Q : Finset ℕ) (N : ℕ) (Y t t₁ : ℝ)
    (hmin : squaredDistance F (mrtArchimedeanTwist t₁) N ≤
      squaredDistance F (mrtArchimedeanTwist t) N) :
    (∑ p ∈ (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)),
      (1 - |Real.cos ((t - t₁) * Real.log (p : ℝ) / 2)|) / (p : ℝ)) ≤
        2 * squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  apply (halasz_prime_cosine_tail_lower F hF N Y t t₁ hmin).trans
  exact mrt_masked_distance_lower F (mrtArchimedeanTwist t) (mrtPrimeMask Q) N
    (fun p hp => hF p (mem_filter.mp hp).2.pos)
    (fun p _ => (mrtArchimedeanTwist_norm t p).le)
    (fun p _ => mrtPrimeMask_bounds Q p)

end TwoPointCorrelations

end OAI
