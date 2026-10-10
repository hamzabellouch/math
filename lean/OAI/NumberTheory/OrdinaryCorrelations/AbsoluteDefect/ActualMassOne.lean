import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.SieveTriangleKernelErrorAt

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral

lemma actualMass_one (h : Squarefree (1:ℕ)) : actualMass 1 1 h = 1 := by
  simp [actualMass, mass, reciprocalSieve, BoundingSieve.selbergTerms]

theorem sparse_harmonic_density (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (u B : ℕ) (hu : 1 ≤ u) (hB : 0 < B) (hBU : B ≤ u^8)
    (hS : S ⊆ Icc (2*B) (4*B)) (ha : ∀ n ∈ S, ‖a n‖ ≤ 1)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u:ℝ)^10) :
    (∑ t ∈ T, ‖∑ n ∈ S, (a n/(n:ℂ))*logPhase t n‖^2) ≤
      (264+3200*(T.card:ℝ)*(u:ℝ)^7/B)*(S.card:ℝ)/(4*(B:ℝ)) := by
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  have hsq : Squarefree (1:ℕ) := squarefree_one
  have he := rough_mellin_energy_at_scale S T (fun n => a n/(n:ℂ)) u B 1 1 hsq
    hu hB hBU (by rfl) (by simpa using (Nat.succ_le_iff.mpr hB)) hS (fun n _ => Nat.coprime_one_right n) hsep hheight
  rw [actualMass_one, inv_one] at he
  norm_num only [Nat.cast_one, one_pow, mul_one] at he
  have hcoef : (∑ n ∈ S, ‖a n/(n:ℂ)‖^2) ≤ (S.card:ℝ)/(4*(B:ℝ)^2) := by
    calc
      _ ≤ ∑ n ∈ S, (1/(2*(B:ℝ)))^2 := by
        apply sum_le_sum
        intro n hn
        apply pow_le_pow_left₀ (norm_nonneg _)
        rw [norm_div, Complex.norm_natCast]
        have hnlo : 2*(B:ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp (hS hn)).1
        exact div_le_div₀ (by norm_num) (ha n hn) (by positivity) hnlo
      _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring
  apply he.trans
  apply (mul_le_mul_of_nonneg_left hcoef (by positivity)).trans_eq
  field_simp

end OrdinarySelbergWeights

end

end OAI
