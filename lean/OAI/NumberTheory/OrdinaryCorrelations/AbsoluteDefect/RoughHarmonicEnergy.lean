import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.RoughMellinEnergy

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral

theorem rough_harmonic_energy (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (u P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hz : 1 ≤ z)
    (hzB : z^2 ≤ u^8) (hS : S ⊆ Icc (2*u^8) (4*u^8))
    (hcop : ∀ n ∈ S, n.Coprime P) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) :
    (∑ t ∈ T, ‖∑ n ∈ S, (a n/(n:ℂ)) * logPhase t n‖^2) ≤
      (264*(actualMass P z hP)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4/u) *
      (44*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4/u)/4 := by
  have hur : (0:ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hc := rough_card_bound S u P z hP hu hz hzB hS hcop
  have hb : (∑ n ∈ S, ‖a n/(n:ℂ)‖^2) ≤
      (44*(u:ℝ)^8*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4*(u:ℝ)^7) / (4*(u:ℝ)^16) := by
    calc
      _ ≤ ∑ n ∈ S, (1/(2*(u:ℝ)^8))^2 := by
        apply sum_le_sum
        intro n hn
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_div, Complex.norm_natCast]
        have hnlo : 2*(u:ℝ)^8 ≤ n := by exact_mod_cast (mem_Icc.mp (hS hn)).1
        exact div_le_div₀ (by norm_num) (ha n hn) (by positivity) hnlo
      _ = (S.card:ℝ)*(1/(4*(u:ℝ)^16)) := by
        simp only [sum_const, nsmul_eq_mul]
        congr 1
        ring
      _ ≤ _ := by
        simpa only [div_eq_mul_inv, one_mul, one_div] using
          mul_le_mul_of_nonneg_right hc (show 0 ≤ (4*(u:ℝ)^16)⁻¹ by positivity)
  have he := rough_mellin_energy S T (fun n => a n/(n:ℂ)) u P z hP hu hz hzB hS hcop hsep hheight
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq
  field_simp

theorem signed_product_energy (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (C : ℝ → ℂ) (u P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hz : 1 ≤ z)
    (hzB : z^2 ≤ u^8) (hS : S ⊆ Icc (2*u^8) (4*u^8))
    (hcop : ∀ n ∈ S, n.Coprime P) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10)
    {ε : ℝ} (hε : 0 ≤ ε) (hC : ∀ t ∈ T, ‖C t‖ ≤ ε) :
    (∑ t ∈ T, ‖C t * ∑ n ∈ S, (a n/(n:ℂ))*logPhase t n‖^2) ≤
      ε^2 * ((264*(actualMass P z hP)⁻¹ + 3200*(T.card:ℝ)*(z:ℝ)^4/u) *
      (44*(actualMass P z hP)⁻¹ + 3200*(z:ℝ)^4/u)/4) := by
  calc
    _ ≤ ∑ t ∈ T, ε^2 * ‖∑ n ∈ S, (a n/(n:ℂ))*logPhase t n‖^2 := by
      apply sum_le_sum
      intro t ht
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hε).mpr (hC t ht)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rough_harmonic_energy S T a u P z hP hu hz hzB hS hcop ha hsep hheight) (sq_nonneg ε)

end OrdinarySelbergWeights

end

end OAI
