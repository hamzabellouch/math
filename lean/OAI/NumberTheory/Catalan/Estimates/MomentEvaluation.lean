import OAI.NumberTheory.Catalan.Analysis.ContactSeries
import OAI.NumberTheory.Catalan.Estimates.MixedOneStart

namespace OAI


noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace InternalCatalan

theorem momentScalar_step (n : ℕ) :
    ((n + 3 : ℕ) : ℚ) * momentScalar (n + 2) =
      ((n + 2 : ℕ) : ℚ) * momentScalar n := by
  rcases Nat.even_or_odd' n with ⟨l, rfl | rfl⟩
  · rw [show 2 * l + 2 = 2 * (l + 1) by omega,
      momentScalar_even, momentScalar_even]
    have hc := centralCoeff_step l
    have hc' := congrArg (fun x : ℚ => ((2 * l + 3 : ℕ) : ℚ) * x) hc
    have hc0 := centralCoeff_ne_zero l
    have hc1 := centralCoeff_ne_zero (l + 1)
    have hden0 : ((2 * l + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    have hden1 : ((2 * (l + 1) + 1 : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast at hc' ⊢
    field_simp
    nlinarith only [hc']
  · rw [show 2 * l + 1 + 2 = 2 * (l + 1) + 1 by omega,
      momentScalar_odd, momentScalar_odd]
    ring

theorem momentScalar_cast_step (n : ℕ) :
    ((n + 3 : ℕ) : ℝ) * (momentScalar (n + 2) : ℝ) =
      ((n + 2 : ℕ) : ℝ) * (momentScalar n : ℝ) := by
  exact_mod_cast momentScalar_step n

private theorem sum_range_sub_add_two (f : ℕ → ℝ) (n : ℕ) :
    (∑ u ∈ Finset.range n, (f u - f (u + 2))) =
      f 0 + f 1 - f n - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

private theorem hasSum_sub_add_two_value (f : ℕ → ℝ)
    (hf : Tendsto f atTop (𝓝 0)) {a : ℝ}
    (ha : HasSum (fun u => f u - f (u + 2)) a) : a = f 0 + f 1 := by
  have ht : Tendsto (fun n => f 0 + f 1 - f n - f (n + 1))
      atTop (𝓝 (f 0 + f 1)) := by
    simpa using
      ((tendsto_const_nhds.sub hf).sub (hf.comp (tendsto_add_atTop_nat 1)))
  have hs := ha.tendsto_sum_nat
  simp only [sum_range_sub_add_two] at hs
  exact tendsto_nhds_unique hs ht

theorem mixedMoment_X_pow_zero_step (d : ℕ) :
    ((d + 2 : ℕ) : ℝ) * mixedMoment (X ^ (d + 2)) (X ^ 0) =
      ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ d) (X ^ 0) +
        (momentScalar d : ℝ) + (momentScalar (d + 1) : ℝ) := by
  have hs := ((hasSum_mixedMoment_X_pow (d + 2) 0).mul_left
      ((d + 2 : ℕ) : ℝ)).sub
    ((hasSum_mixedMoment_X_pow d 0).mul_left ((d + 1 : ℕ) : ℝ))
  have hs' : HasSum
      (fun u => (momentScalar (d + u) : ℝ) - (momentScalar (d + u + 2) : ℝ))
      (((d + 2 : ℕ) : ℝ) * mixedMoment (X ^ (d + 2)) (X ^ 0) -
        ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ d) (X ^ 0)) := by
    convert hs using 1
    ext u
    have hrec := momentScalar_cast_step (d + u)
    have he : d + 2 + u = d + u + 2 := by omega
    simp only [Nat.zero_add, he]
    have hu : (u : ℝ) + 1 ≠ 0 := by positivity
    push_cast at hrec ⊢
    field_simp [hu]
    nlinarith only [hrec]
  have hlim : Tendsto (fun u => (momentScalar (d + u) : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.add_comm d] using
      tendsto_momentScalar_zero.comp (tendsto_add_atTop_nat d)
  have hv := hasSum_sub_add_two_value _ hlim hs'
  simp only [Nat.add_zero] at hv
  linarith

theorem mixedMoment_X_one_zero : mixedMoment (X ^ 1) (X ^ 0) = 2 := by
  have hs := (hasSum_nat_add_iff' 1).mpr (hasSum_mixedMoment_X_pow 1 0)
  have hs' : HasSum
      (fun u => (momentScalar u : ℝ) - (momentScalar (u + 2) : ℝ))
      (mixedMoment (X ^ 1) (X ^ 0)) := by
    convert hs using 1
    · ext u
      have hrec := momentScalar_cast_step u
      have hu : (u : ℝ) + 2 ≠ 0 := by positivity
      simp only [Nat.zero_add, show 1 + (u + 1) = u + 2 by omega]
      push_cast at hrec ⊢
      field_simp [hu]
      nlinarith only [hrec]
    · simp [momentScalar_odd 0]
  have hv := hasSum_sub_add_two_value _ tendsto_momentScalar_zero hs'
  simpa [momentScalar_odd 0] using hv

theorem mixedMoment_zero_X_pow_step (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ 0) (X ^ (d + 2)) =
      (d : ℝ) * mixedMoment (X ^ 0) (X ^ d) + 2 / ((d + 1 : ℕ) : ℝ) := by
  have htail := (hasSum_nat_add_iff' 2).mpr (hasSum_mixedMoment_X_pow 0 d)
  have htail' : HasSum
      (fun u => (momentScalar (u + 2) : ℝ) / ((d + u + 3 : ℕ) : ℝ))
      (mixedMoment (X ^ 0) (X ^ d) - 2 / ((d + 1 : ℕ) : ℝ)) := by
    convert htail using 1
    · ext u
      simp only [Nat.zero_add]
      congr 2
    · simp [Finset.sum_range_succ, momentScalar_odd 0]
  have hs := ((hasSum_mixedMoment_X_pow 0 (d + 2)).mul_left
      ((d + 1 : ℕ) : ℝ)).sub (htail'.mul_left (d : ℝ))
  have hs' : HasSum
      (fun u => (momentScalar u : ℝ) - (momentScalar (u + 2) : ℝ))
      (((d + 1 : ℕ) : ℝ) * mixedMoment (X ^ 0) (X ^ (d + 2)) -
        (d : ℝ) * (mixedMoment (X ^ 0) (X ^ d) - 2 / ((d + 1 : ℕ) : ℝ))) := by
    convert hs using 1
    ext u
    have hrec := momentScalar_cast_step u
    have he : d + 2 + u + 1 = d + u + 3 := by omega
    simp only [Nat.zero_add, he]
    have hu : (d : ℝ) + (u : ℝ) + 3 ≠ 0 := by positivity
    push_cast at hrec ⊢
    field_simp [hu]
    nlinarith only [hrec]
  have hv := hasSum_sub_add_two_value _ tendsto_momentScalar_zero hs'
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  simp only [momentScalar_zero, momentScalar_odd 0, Rat.cast_ofNat,
    Rat.cast_zero, add_zero] at hv
  push_cast at hv ⊢
  field_simp [hd] at hv ⊢
  nlinarith only [hv]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

theorem mixedMoment_minus_decomposition (d : ℕ) :
    mixedMoment (X ^ d) (X ^ 0) = (boundaryMinus d : ℝ) +
      mixedMoment 1 1 * (centralCoeffKernel (d : ℤ) : ℝ) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases d with
      | zero =>
        simpa [centralCoeffKernel] using mixedMoment_X_one_zero
      | succ d =>
        change mixedMoment (X ^ (d + 2)) (X ^ 0) = (boundaryMinus (d + 2) : ℝ) +
          mixedMoment 1 1 * (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℝ)
        have ha := mixedMoment_X_pow_zero_step d
        rw [ih d (by omega)] at ha
        have hr : ((d + 2 : ℕ) : ℝ) * (boundaryMinus (d + 2) : ℝ) =
            ((d + 1 : ℕ) : ℝ) * (boundaryMinus d : ℝ) +
              (momentScalar d : ℝ) + (momentScalar (d + 1) : ℝ) := by
          exact_mod_cast boundaryMinus_step d
        have hc : ((d + 2 : ℕ) : ℝ) *
              (centralCoeffKernel ((d + 2 : ℕ) : ℤ) : ℝ) =
            ((d + 1 : ℕ) : ℝ) * (centralCoeffKernel (d : ℤ) : ℝ) := by
          exact_mod_cast centralCoeffKernel_nat_step d
        have hstart := congrArg (fun x : ℝ => mixedMoment 1 1 * x) hc
        have hd : ((d + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hd
        nlinarith only [ha, hr, hstart]

theorem mixedMoment_plus_succ_decomposition (u : ℕ) :
    mixedMoment (X ^ 0) (X ^ (u + 1)) = (boundaryPlus (u + 1) : ℝ) +
      mixedMoment 1 X * (centralCoeffKernel (u : ℤ) : ℝ) := by
  induction u using Nat.strong_induction_on with
  | h u ih =>
    cases u with
    | zero => simp
    | succ u =>
      cases u with
      | zero =>
        have ha := mixedMoment_zero_X_pow_step 0
        norm_num at ha
        simpa [boundaryPlus, centralCoeffKernel] using ha
      | succ u =>
        change mixedMoment (X ^ 0) (X ^ (u + 2 + 1)) =
          (boundaryPlus (u + 2 + 1) : ℝ) +
            mixedMoment 1 X * (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℝ)
        have ha := mixedMoment_zero_X_pow_step (u + 1)
        rw [ih u (by omega)] at ha
        have hr : ((u + 1 + 1 : ℕ) : ℝ) * (boundaryPlus (u + 1 + 2) : ℝ) =
            ((u + 1 : ℕ) : ℝ) * (boundaryPlus (u + 1) : ℝ) +
              2 / ((u + 1 + 1 : ℕ) : ℝ) := by
          have hr0 := congrArg (fun x : ℚ => (x : ℝ)) (boundaryPlus_step (u + 1))
          push_cast at hr0 ⊢
          exact hr0
        have hc : ((u + 2 : ℕ) : ℝ) *
              (centralCoeffKernel ((u + 2 : ℕ) : ℤ) : ℝ) =
            ((u + 1 : ℕ) : ℝ) * (centralCoeffKernel (u : ℤ) : ℝ) := by
          exact_mod_cast centralCoeffKernel_nat_step u
        have hstart := congrArg (fun x : ℝ => mixedMoment 1 X * x) hc
        have hu : ((u + 2 : ℕ) : ℝ) ≠ 0 := by positivity
        apply mul_left_cancel₀ hu
        nlinarith only [ha, hr, hstart]

theorem mixedMoment_X_pow_decomposition (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) = (momentRat i j : ℝ) +
      mixedMoment 1 1 * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ) +
      mixedMoment 1 X * (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℝ) := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => norm_num [centralCoeffKernel]
    | succ j =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((j + 1 : ℕ) : ℤ)) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      have he : ((j + 1 : ℕ) : ℤ) - (0 : ℤ) - 1 = (j : ℤ) := by omega
      simp only [Nat.cast_zero]
      rw [momentRat_zero_left, hn, he]
      simpa using mixedMoment_plus_succ_decomposition j
  | succ i ih =>
    cases j with
    | zero =>
      have hn : centralCoeffKernel ((0 : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) = 0 :=
        centralCoeffKernel_of_neg (by omega)
      simp only [Nat.cast_zero]
      rw [momentRat_zero_right, hn]
      simpa using mixedMoment_minus_decomposition (i + 1)
    | succ j =>
      have ha := mixedMoment_X_pow_step i j
      have hr : (momentRat i j : ℝ) - (momentRat (i + 1) (j + 1) : ℝ) =
          (momentScalar i : ℝ) / ((j + 1 : ℕ) : ℝ) := by
        exact_mod_cast momentRat_step i j
      have hd : ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) =
          (i : ℤ) - (j : ℤ) := by omega
      have he : ((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1 =
          (j : ℤ) - (i : ℤ) - 1 := by omega
      change mixedMoment (X ^ (i + 1)) (X ^ (j + 1)) =
        (momentRat (i + 1) (j + 1) : ℝ) +
          mixedMoment 1 1 * (centralCoeffKernel (((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ)) : ℝ) +
          mixedMoment 1 X *
            (centralCoeffKernel (((j + 1 : ℕ) : ℤ) - ((i + 1 : ℕ) : ℤ) - 1) : ℝ)
      rw [hd, he]
      rw [ih j] at ha
      linarith only [ha, hr]

end InternalCatalan

end



noncomputable section

open Polynomial

namespace InternalCatalan

theorem mixedMoment_X_pow_evaluation (i j : ℕ) :
    mixedMoment (X ^ i) (X ^ j) = (momentRat i j : ℝ) +
      4 * catalan * (centralCoeffKernel ((i : ℤ) - (j : ℤ)) : ℝ) +
      (3 / 2 : ℝ) * zetaSeries 0 0 *
        (centralCoeffKernel ((j : ℤ) - (i : ℤ) - 1) : ℝ) := by
  have hzero : mixedMoment 1 1 = 4 * catalan := by
    simpa only [pow_zero] using mixedMoment_zero_zero
  have hone : mixedMoment 1 X = (3 / 2 : ℝ) * zetaSeries 0 0 := by
    simpa only [pow_zero, pow_one] using mixedMoment_zero_one
  rw [mixedMoment_X_pow_decomposition, hzero, hone]

end InternalCatalan

end

end OAI
