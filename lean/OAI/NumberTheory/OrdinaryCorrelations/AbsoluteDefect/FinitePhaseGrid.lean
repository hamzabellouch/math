import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ForwardSum

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

namespace OrdinaryTwistWidth
open OrdinaryCorrelations OrdinaryInitialWidth OrdinaryLocalAdditive Finset Filter MeasureTheory

lemma finite_phase_grid (C : ℝ) (hC : 0≤C) {δ : ℝ} (hδ : 0<δ) :
    ∃N : ℕ, 0<N ∧ ∀t : ℝ, ∃j : Fin N, C*|Int.fract t-(j:ℝ)/N|≤δ := by
  let N : ℕ := ⌈(C+1)/δ⌉₊
  have hN : 0<N := Nat.ceil_pos.mpr (div_pos (by linarith) hδ)
  have hNreal : (0:ℝ)<N := by exact_mod_cast hN
  have hsize : C+1≤δ*N := by
    have hh : (C+1)/δ≤(N:ℝ) := Nat.le_ceil _
    have ht := (div_le_iff₀ hδ).mp hh
    linarith
  refine ⟨N,hN,?_⟩
  intro t
  let j : ℕ := ⌊Int.fract t*N⌋₊
  have harg : 0≤Int.fract t*(N:ℝ) := mul_nonneg (Int.fract_nonneg t) hNreal.le
  have hj : j<N := (Nat.floor_lt harg).mpr (by nlinarith [Int.fract_lt_one t])
  refine ⟨⟨j,hj⟩,?_⟩
  have hfloor : (j:ℝ)≤Int.fract t*N := Nat.floor_le harg
  have hfloor' : Int.fract t*N<(j:ℝ)+1 := Nat.lt_floor_add_one _
  change C*|Int.fract t-(j:ℝ)/N|≤δ
  have hdiff0 : 0≤Int.fract t-(j:ℝ)/N := by
    have hh := (div_le_iff₀ hNreal).mpr hfloor
    linarith
  have hdiff1 : Int.fract t-(j:ℝ)/N≤1/(N:ℝ) := by
    apply (le_div_iff₀ hNreal).mpr
    have he : (Int.fract t-(j:ℝ)/N)*N=Int.fract t*N-j := by field_simp
    rw [he]
    linarith
  rw [abs_of_nonneg hdiff0]
  apply (mul_le_mul_of_nonneg_left hdiff1 hC).trans
  have he : C*(1/(N:ℝ))=C/N := by ring
  rw [he,div_le_iff₀ hNreal]
  linarith

end OrdinaryTwistWidth

end

end OAI
