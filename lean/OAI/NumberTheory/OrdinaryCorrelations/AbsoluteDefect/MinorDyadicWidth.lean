import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NormPhase
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.FixedBudget
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AccuracyCancel
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DyadicL1LeDiscrete

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
open OrdinaryCorrelations OrdinaryNarrowGrid OrdinaryRationalWidth OrdinaryLocalAdditive
open OrdinarySharpWindow Finset Filter MeasureTheory

lemma minor_dyadic_width (A c k v t m : ℕ)
    (hL : 1≤∑p∈primeWindow 1 (primeStart m) (primeSpan t m),(p:ℝ)⁻¹)
    (hrough : Real.exp (-(∑p∈primeWindow 1 (primeStart m) (primeSpan t m),(p:ℝ)⁻¹))≤accuracy m)
    (hres : (primeSpan t m:ℝ)*Real.sqrt (4/((2^(10*m):ℕ):ℝ))≤accuracy m)
    {f : ℕ→ℂ} (hf : OneBounded f) (hm : Multiplicative f) :
    ∀ᶠ X : ℕ in atTop, ∀q : ℕ, 2^(10*m)≤q → q≤approxBound A c k v t m →
    ∀a : ℤ, Int.gcd a q=1 → ∀α : ℝ,
    |α-(a:ℝ)/q|≤1/(2*(q:ℝ)*primeEnd t m) →
      (∫x : ℝ,‖sharpWindow (Ioc X (2*X))
        (fun n=>f n*phase (α*n)) (fun n=>(n:ℝ)) (shortWidth A c k v t m:ℝ) x‖)
      ≤55*accuracy m*shortWidth A c k v t m*X := by
  let S := shortWidth A c k v t m
  let ε := accuracy m
  have hε : 0<ε := accuracy_pos m
  have hS : 0<S := shortWidth_pos A c k v t m
  have hSr : (0:ℝ)<S := by exact_mod_cast hS
  have hb : Real.exp (-(∑p∈primeWindow 1 (primeStart m) (primeSpan t m),(p:ℝ)⁻¹))+
      12*(3/4:ℝ)^primeStart m+2/(2:ℝ)^primeStart m+
      (primeSpan t m:ℝ)*(Real.sqrt (4/((2^(10*m):ℕ):ℝ))+
      Real.sqrt (8*(approxBound A c k v t m:ℝ)*primeEnd t m/S))+ε≤18*ε := by
    have hdiag := diagonal_small m
    have hsq := square_small m
    have hsm := smooth_loss_small A c k v t m
    change _≤accuracy m at hsm
    dsimp only [ε,S]
    nlinarith only [hrough,hres,hdiag,hsq,hsm]
  have hM := minor_arc_explicit_width (primeStart m) (primeSpan t m) S
    (2^(10*m)) (approxBound A c k v t m) hS (by positivity) hL hf hm hε
  have hsmall : ∀ᶠ U : ℕ in atTop,∀q : ℕ,2^(10*m)≤q → q≤approxBound A c k v t m →
      ∀a : ℤ,Int.gcd a q=1 → ∀α : ℝ,|α-(a:ℝ)/q|≤1/(2*(q:ℝ)*primeEnd t m) →
      (∑y∈range U,‖∑j∈range S,f (y+1+j)*phase (α*(y+1+j))‖)≤18*ε*S*(U+S) := by
    filter_upwards [hM] with U hU
    intro q hq hqN a ha α hα
    have hh := hU q hq hqN a ha α (by simpa only [primeEnd,Nat.cast_pow,Nat.cast_ofNat] using hα)
    apply hh.trans
    have hbc : _≤18*ε := hb
    have hh' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbc (Nat.cast_nonneg S))
      (show 0≤(U:ℝ)+S by positivity)
    simpa only [primeEnd,Nat.cast_pow,Nat.cast_ofNat] using hh'
  have ht : Tendsto (fun X : ℕ=>2*X) atTop atTop :=
    tendsto_atTop_mono (fun X : ℕ=>by dsimp only [id];omega) tendsto_id
  obtain ⟨B,hB⟩ := exists_nat_ge ((36*ε+4)*(S:ℝ)/ε)
  filter_upwards [hsmall,ht.eventually hsmall,eventually_ge_atTop B] with X hX h2X hXB
  intro q hq hqN a ha α hα
  have h1 := hX q hq hqN a ha α hα
  have h2 := h2X q hq hqN a ha α hα
  have hB' : (36*ε+4)*(S:ℝ)≤ε*X := by
    have hh := hB.trans (show (B:ℝ)≤X by exact_mod_cast hXB)
    have hg := (div_le_iff₀ hε).mp hh
    nlinarith only [hg]
  have herr := mul_le_mul_of_nonneg_right hB' hSr.le
  have hbnd : OneBounded (fun n=>f n*phase (α*n)) := by
    intro n;rw [norm_mul,norm_phase,mul_one];exact hf n
  have hi := dyadic_l1_le_discrete hbnd X S
  push_cast at h2 hi
  change _≤55*ε*S*X
  nlinarith only [hi,h1,h2,herr]

end OrdinaryUniformWidth

end

end OAI
