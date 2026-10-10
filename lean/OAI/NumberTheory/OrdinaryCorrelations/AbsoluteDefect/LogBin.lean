import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.KernelBinBound

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

namespace OrdinaryDirichletMeanSquare
open ArithmeticFunction

def logBin (n : ℕ) : ℕ := ⌊Real.log n⌋₊

def mangoldtCoefficient (f : ℕ → ℂ) (δ : ℝ) (n : ℕ) : ℂ :=
  f n * ((ArithmeticFunction.vonMangoldt n * Real.exp (-(1+δ)*Real.log n) : ℝ) : ℂ)

def chebyshevConstant : ℝ := Real.log 4 + 4

lemma chebyshevConstant_pos : 0 < chebyshevConstant := by
  unfold chebyshevConstant
  have := Real.log_pos (show (1:ℝ)<4 by norm_num)
  linarith

lemma logBin_bounds (n : ℕ) :
    (logBin n : ℝ) ≤ Real.log n ∧ Real.log n < (logBin n : ℝ)+1 := by
  exact ⟨Nat.floor_le (Real.log_natCast_nonneg n),Nat.lt_floor_add_one _⟩

lemma logBin_close (n : ℕ) : |Real.log n-logBin n| ≤ 1 := by
  have h := logBin_bounds n
  rw [abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith

lemma mangoldt_coefficient_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (δ : ℝ) (n : ℕ) :
    ‖mangoldtCoefficient f δ n‖ ≤
      ArithmeticFunction.vonMangoldt n * Real.exp (-(1+δ)*Real.log n) := by
  unfold mangoldtCoefficient
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)]
  simpa using mul_le_mul_of_nonneg_right (hf n)
    (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_pos _).le)

lemma mangoldt_bin_mass (s : Finset ℕ) (hs : ∀ n ∈ s, 0 < n)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ) (j : ℕ) :
    ∑ n ∈ s.filter (fun n => logBin n=j), ‖mangoldtCoefficient f δ n‖ ≤
      chebyshevConstant * Real.exp 1 * Real.exp (-δ*j) := by
  classical
  let S := s.filter (fun n => logBin n=j)
  have hll (n : ℕ) (hn : n ∈ S) : (j : ℝ) ≤ Real.log n ∧ Real.log n < (j:ℝ)+1 := by
    simpa only [(Finset.mem_filter.mp hn).2] using logBin_bounds n
  have hsub : S ⊆ Finset.Ioc 0 ⌊Real.exp ((j:ℝ)+1)⌋₊ := by
    intro n hn
    refine Finset.mem_Ioc.mpr ⟨hs n (Finset.mem_filter.mp hn).1,?_⟩
    apply Nat.le_floor
    exact (Real.exp_log (x:=(n:ℝ)) (by exact_mod_cast hs n (Finset.mem_filter.mp hn).1) ▸
      (Real.exp_lt_exp.mpr (hll n hn).2).le)
  have hψ : ∑ n ∈ S, ArithmeticFunction.vonMangoldt n ≤
      chebyshevConstant * Real.exp ((j:ℝ)+1) := by
    calc
      _ ≤ Chebyshev.psi (Real.exp ((j:ℝ)+1)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro n _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ _ := Chebyshev.psi_le_const_mul_self (Real.exp_pos _).le
  calc
    _ ≤ ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * Real.exp (-(1+δ)*j) := by
      apply Finset.sum_le_sum
      intro n hn
      apply (mangoldt_coefficient_bound f hf δ n).trans
      apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left (hll n hn).1 (show 0 ≤ 1+δ by linarith)
      linarith
    _ = (∑ n ∈ S, ArithmeticFunction.vonMangoldt n) * Real.exp (-(1+δ)*j) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (chebyshevConstant * Real.exp ((j:ℝ)+1)) * Real.exp (-(1+δ)*j) :=
      mul_le_mul_of_nonneg_right hψ (Real.exp_pos _).le
    _ = _ := by
      rw [mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
      congr 2
      ring

theorem mangoldt_gaussian_energy (s : Finset ℕ) (hs : ∀ n ∈ s, 0<n)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) {δ : ℝ} (hδ : 0<δ) :
    (∫ x : ℝ, gaussian x *
      ‖polynomial s (mangoldtCoefficient f δ) (fun n => Real.log n) x‖^2) ≤
      gaussianConstant * Real.exp 3 * 4 *
        (chebyshevConstant * Real.exp 1)^2 * (2+1/δ) := by
  classical
  apply (binned_gaussian_energy s (mangoldtCoefficient f δ) (fun n => Real.log n) logBin
    (fun n _ => logBin_close n)).trans
  have hgeom : ∑ j ∈ s.image logBin, Real.exp (-(2*δ)*(j:ℝ)) ≤ 2+1/δ := by
    have h := geometric_exponential_row (s.image logBin) 0 (show 0<2*δ by linarith)
    have hr : (2:ℝ)/(2*δ) = 1/δ := by field_simp
    simpa only [Nat.dist_zero_left,hr] using h
  have hmass : (∑ j ∈ s.image logBin,
      (∑ n ∈ s.filter (fun n => logBin n=j), ‖mangoldtCoefficient f δ n‖)^2) ≤
        (chebyshevConstant * Real.exp 1)^2 * (2+1/δ) := by
    calc
      _ ≤ ∑ j ∈ s.image logBin,
          (chebyshevConstant*Real.exp 1)^2 * Real.exp (-(2*δ)*(j:ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := pow_le_pow_left₀
          (Finset.sum_nonneg (fun n _ => norm_nonneg (mangoldtCoefficient f δ n)))
          (mangoldt_bin_mass s hs f hf hδ.le j) 2
        apply h.trans_eq
        rw [mul_pow,←Real.exp_nat_mul]
        congr 1
        congr 1
        ring
      _ = (chebyshevConstant*Real.exp 1)^2 *
          ∑ j ∈ s.image logBin, Real.exp (-(2*δ)*(j:ℝ)) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (sq_nonneg _)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ gaussianConstant*Real.exp 3*4 by unfold gaussianConstant; positivity)

end OrdinaryDirichletMeanSquare

end

end OAI
