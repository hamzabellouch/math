import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShiftedDual

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
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryShortDual

def unitDual (z : ℂ) : ℂ := (‖z‖:ℂ)⁻¹*star z

lemma unitDual_bound (z : ℂ) : ‖unitDual z‖≤1 := by
  by_cases hz : z=0
  · simp [unitDual,hz]
  have hn : ‖z‖≠0 := norm_ne_zero_iff.mpr hz
  simp only [unitDual,norm_mul,norm_inv,norm_star,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z),inv_mul_cancel₀ hn,le_refl]

lemma unitDual_mul (z : ℂ) : unitDual z*z=(‖z‖:ℂ) := by
  by_cases hz : z=0
  · simp [unitDual,hz]
  have hn : (‖z‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
  unfold unitDual
  rw [mul_assoc,mul_comm (star z) z]
  rw [Complex.star_def,Complex.mul_conj']
  field_simp

def shortSum (F : ℕ → ℂ) (D y : ℕ) : ℂ := ∑k∈range D,F (y+1+k)

def actualDual (F : ℕ → ℂ) (D U : ℕ) : ℕ → ℂ :=
  shiftedDual (fun y => unitDual (shortSum F D y)) D U

lemma actualDual_bound (F : ℕ → ℂ) (D U n : ℕ) :
    ‖actualDual F D U n‖≤1 :=
  shiftedDual_bound _ (fun y => unitDual_bound (shortSum F D y)) D U n

lemma actualDual_zero (F : ℕ → ℂ) (D U n : ℕ) (hn : n<D ∨ U+D≤n) :
    actualDual F D U n=0 := by
  unfold actualDual shiftedDual
  split_ifs with h
  · rcases hn with hn | hn <;> omega
  · rfl

theorem actual_short_dual_witness (F : ℕ → ℂ) (D U : ℕ) :
    (D:ℝ)⁻¹*(∑y∈range U,‖shortSum F D y‖)=
      ‖∑m∈range (U+D),F m*((D:ℂ)⁻¹*∑j∈range D,actualDual F D U (m+j))‖ := by
  let c := fun y => unitDual (shortSum F D y)
  let u := shiftedDual c D U
  have hi : ((∑y∈range U,‖shortSum F D y‖:ℝ):ℂ)=
      ∑m∈range (U+D),F m*∑j∈range D,u (m+j) := by
    calc
      _ = ∑y∈range U,c y*shortSum F D y := by
        simp only [Complex.ofReal_sum,c,unitDual_mul]
      _ = _ := dual_fubini c F D U
  have he : (D:ℂ)⁻¹*((∑y∈range U,‖shortSum F D y‖:ℝ):ℂ)=
      ∑m∈range (U+D),F m*((D:ℂ)⁻¹*∑j∈range D,u (m+j)) := by
    rw [hi,mul_sum]
    apply sum_congr rfl
    intro m hm
    ring
  have hs : 0≤∑y∈range U,‖shortSum F D y‖ := sum_nonneg (fun y hy => norm_nonneg _)
  have hh := congrArg norm he
  simpa only [norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hs,u,c,actualDual] using hh

theorem actual_short_dual (F : ℕ → ℂ) (D U : ℕ) :
    ∃u : ℕ → ℂ, (∀n,‖u n‖≤1) ∧
      (D:ℝ)⁻¹*(∑y∈range U,‖shortSum F D y‖)=
        ‖∑m∈range (U+D),F m*((D:ℂ)⁻¹*∑j∈range D,u (m+j))‖ :=
  ⟨actualDual F D U,actualDual_bound F D U,actual_short_dual_witness F D U⟩

end OrdinaryShortDual

end

end OAI
