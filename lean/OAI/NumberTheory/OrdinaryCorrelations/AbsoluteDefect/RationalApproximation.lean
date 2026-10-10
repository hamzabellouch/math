import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase

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

namespace OrdinaryUniformWidth
open OrdinaryCorrelations OrdinaryLocalAdditive

lemma rational_approximation (α : ℝ) {N : ℕ} (hN : 0<N) :
    ∃q : ℕ, 0<q ∧ q≤N ∧ ∃a : ℤ, Int.gcd a q=1 ∧ -(q:ℤ)≤a ∧ a≤2*(q:ℤ) ∧
      |Int.fract α-(a:ℝ)/q|≤1/(((N:ℝ)+1)*q) := by
  obtain ⟨r,hr,hrN⟩ := Real.exists_rat_abs_sub_le_and_den_le (Int.fract α) hN
  refine ⟨r.den,r.den_pos,hrN,r.num,?_,?_,?_,?_⟩
  · simpa only [Int.gcd,Int.natAbs_natCast] using r.reduced.gcd_eq_one
  · have hden : (1:ℝ)≤r.den := by exact_mod_cast r.den_pos
    have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
    have hbound : 1/(((N:ℝ)+1)*r.den)≤1 := by apply (div_le_one₀ (by positivity)).mpr;nlinarith only [hden,hN0]
    have hh := (abs_le.mp (hr.trans hbound)).2
    have hf := Int.fract_nonneg α
    rw [Rat.cast_def] at hh
    have hl : -(1:ℝ)≤(r.num:ℝ)/r.den := by linarith only [hh,hf]
    have hn := (le_div_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mp hl
    have hn' : -(r.den:ℝ)≤r.num := by linarith only [hn]
    exact_mod_cast hn'
  · have hden : (1:ℝ)≤r.den := by exact_mod_cast r.den_pos
    have hN0 : (0:ℝ)≤N := Nat.cast_nonneg _
    have hbound : 1/(((N:ℝ)+1)*r.den)≤1 := by apply (div_le_one₀ (by positivity)).mpr;nlinarith only [hden,hN0]
    have hh := (abs_le.mp (hr.trans hbound)).1
    have hf := Int.fract_lt_one α
    rw [Rat.cast_def] at hh
    have hl : (r.num:ℝ)/r.den≤2 := by linarith only [hh,hf]
    have hn := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).mp hl
    exact_mod_cast hn
  · simpa only [Rat.cast_def] using hr

lemma phase_fract (α : ℝ) (n : ℕ) : phase (α*n)=phase (Int.fract α*n) := by
  have he : α*(n:ℝ)=Int.fract α*n+((Int.floor α*(n:ℤ):ℤ):ℝ) := by
    rw [Int.fract];push_cast;ring
  rw [he,phase_add,phase_int,mul_one]

end OrdinaryUniformWidth

end

end OAI
