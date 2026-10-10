import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogPhaseMulConj

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace OrdinarySelbergWeights
open Finset OrdinaryLogIntegral OrdinarySparseSieve

theorem rough_mellin_energy (S : Finset ℕ) (T : Finset ℝ) (a : ℕ → ℂ)
    (u P z : ℕ) (hP : Squarefree P) (hu : 1 ≤ u) (hz : 1 ≤ z)
    (hzB : z^2 ≤ u^8) (hS : S ⊆ Icc (2*u^8) (4*u^8))
    (hcop : ∀ n ∈ S, n.Coprime P)
    (hsep : (T : Set ℝ).Pairwise (fun x y => 1 ≤ |x-y|))
    (hheight : ∀ t ∈ T, ∀ s ∈ T, |t-s| ≤ (u : ℝ)^10) :
    (∑ t ∈ T, ‖∑ n ∈ S, a n * logPhase t n‖^2) ≤
      (264*(u : ℝ)^8*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7) * (∑ n ∈ S, ‖a n‖^2) := by
  have hG : 0 ≤ actualMass P z hP := (mass_pos (reciprocalSieve P hP) hz).le
  have hp : 0 < u^8 := pow_pos (by omega) _
  have hsA : S ⊆ range (6*u^8+1) := by
    intro n hn
    have hh := mem_Icc.mp (hS hn)
    simp only [mem_range]
    omega
  have hh := sparse_majorant_duality S (range (6*u^8+1)) T a
    (triangleSieveMajorant (u^8) P z hP)
    (fun t n => logPhase t (max ((u^8 : ℕ) : ℝ) n)) hsA
    (fun n _ => triangleSieveMajorant_nonneg _ _ _ _ hP)
    (fun n hn => triangleSieveMajorant_one hP hz hp (hS hn) (hcop n hn))
    (show 0 ≤ 264*(u : ℝ)^8*(actualMass P z hP)⁻¹ +
        3200*(T.card : ℝ)*(z : ℝ)^4*(u : ℝ)^7 by positivity)
    (fun t ht => sparse_rough_gram_row T u P z hP hu hz hzB hsep hheight t ht)
  have he : ∀ t, (∑ n ∈ S, a n * logPhase t (max ((u^8 : ℕ) : ℝ) n)) =
      ∑ n ∈ S, a n * logPhase t n := by
    intro t
    apply sum_congr rfl
    intro n hn
    have hh := (mem_Icc.mp (hS hn)).1
    have hnB : u^8 ≤ n := by omega
    rw [max_eq_right (by exact_mod_cast hnB)]
  simpa only [he] using hh

theorem rough_card_bound (S : Finset ℕ) (u P z : ℕ) (hP : Squarefree P)
    (hu : 1 ≤ u) (hz : 1 ≤ z) (hzB : z^2 ≤ u^8)
    (hS : S ⊆ Icc (2*u^8) (4*u^8)) (hcop : ∀ n ∈ S, n.Coprime P) :
    (S.card : ℝ) ≤ 44*(u : ℝ)^8*(actualMass P z hP)⁻¹ +
      3200*(z : ℝ)^4*(u : ℝ)^7 := by
  have hp : 0 < u^8 := pow_pos (by omega) _
  have hsA : S ⊆ range (6*u^8+1) := by
    intro n hn
    have hh := mem_Icc.mp (hS hn)
    simp only [mem_range]
    omega
  have hmajor : (S.card : ℝ) ≤ ∑ n ∈ range (6*u^8+1), triangleSieveMajorant (u^8) P z hP n := by
    calc
      _ = ∑ n ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ n ∈ S, triangleSieveMajorant (u^8) P z hP n := sum_le_sum (fun n hn =>
        triangleSieveMajorant_one hP hz hp (hS hn) (hcop n hn))
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsA (fun n _ _ =>
        triangleSieveMajorant_nonneg _ _ _ _ hP)
  have he : ((∑ n ∈ range (6*u^8+1), triangleSieveMajorant (u^8) P z hP n : ℝ) : ℂ) =
      2*sieveTriangleKernel 0 (u^8) P z hP := by
    have hg := triangleSieveGram (u^8) P z hP 0 0
    simp only [sub_self] at hg
    rw [← hg]
    simp [weightedGram, logPhase]
  have hn : 0 ≤ ∑ n ∈ range (6*u^8+1), triangleSieveMajorant (u^8) P z hP n :=
    sum_nonneg (fun n _ => triangleSieveMajorant_nonneg _ _ _ _ hP)
  have hnorm := congrArg norm he
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn, norm_mul, Complex.norm_ofNat] at hnorm
  have hb := sieveTriangleKernel_norm 0 u P z hP hu hz hzB (by simp)
  norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero,
    inv_one, mul_one] at hb
  rw [hnorm] at hmajor
  nlinarith

end OrdinarySelbergWeights

end

end OAI
