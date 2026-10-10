import OAI.Analysis.FreeEntropy.TwoNoiseFisher

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace FiniteEntropySeparation
open Finset FreeSeries
namespace FreeSeries
variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
theorem cumulants_one [DecidableEq α] (M : Series α) (hM : M [] = 1) (i : α) :
    cumulants M [i] = M [i] := by
  have he := congrFun (cumulants_equation hM) [i]
  simpa [subst_cons, hM, conv_nil] using he.symm
 theorem cumulants_two (M : Series α) (hM : M [] = 1) (i j : α) :
    cumulants M [i,j] = M [i,j] - M [i] * M [j] := by
  have he := congrFun (cumulants_equation hM) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, hM, one_mul,
    subst_nil, conv_nil, FreeSeries.deriv_apply] at he
  rw [cumulants_one M hM i] at he
  linear_combination -he
 theorem residual_short {R : Series α} {v : α → ℝ}
    (hc : ∀ i, R [i] = 0) (hv : ∀ i j, R [i,j] = if j=i then (v i : ℂ) else 0)
    (i : α) (w : List α) (hw : w.length < 2) : residual R v i w = 0 := by
  cases w with
  | nil => simp [residual, hc]
  | cons j w =>
    have : w = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hw; omega)
    subst w
    simp [residual, hv, letter]
 theorem residual_long (R : Series α) (v : α → ℝ) (i : α) (w : List α) (hw : 2 ≤ w.length) :
    residual R v i w = R (i::w) := by
  cases w with
  | nil => simp at hw
  | cons j w =>
    cases w with
    | nil => simp at hw
    | cons k w => simp [residual, letter]
end FreeSeries
namespace Model
open FreeTensor
variable (p : ℕ) [NeZero p]
def variance (i : Fin (p+1)) : ℝ := ‖C p i (τ p).vacuum‖ ^ 2
 theorem variance_nonneg (i : Fin (p+1)) : 0 ≤ variance p i := sq_nonneg _

omit [NeZero p] in
theorem fockMoments_one [NeZero p] (i : Fin p) : fockMoments p [i] = 0 := by
  have he := congrFun (fockMoments_eq p) [i]
  simpa [subst_cons, conv_nil, quadratic] using he

omit [NeZero p] in
theorem fockMoments_two [NeZero p] (i j : Fin p) : fockMoments p [i,j] = if j=i then 1 else 0 := by
  have he := congrFun (fockMoments_eq p) [i,j]
  simp only [Pi.add_apply, unit_cons, zero_add, subst_cons, conv_cons, subst_nil, conv_nil,
    FreeSeries.deriv_apply, quadratic] at he
  simpa [fockMoments] using he
 theorem C_centered (hp : 2 ≤ p) (i : Fin (p+1)) : signalMoments p [i] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    simpa [signalMoments, wordMoment, wordEval] using
      (trace_equidiscreteSignal (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp)
  | cast i =>
    have he := signal_option_moments p [some i]
    simpa [fockMoments_one] using he
 theorem C_offDiagonal (i j : Fin (p+1)) (hij : j ≠ i) : signalMoments p [i,j] = 0 := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => exact (hij rfl).elim
    | cast j =>
      have he := signal_option_moments p [none, some j]
      simpa [fockMoments_one] using he
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      have he := signal_option_moments p [some i, none]
      simpa [fockMoments_one] using he
    | cast j =>
      have hj : j ≠ i := fun h => hij (congrArg Fin.castSucc h)
      have he := signal_option_moments p [some i, some j]
      simpa [fockMoments_two, hj] using he
 theorem C_covariance (i j : Fin (p+1)) :
    signalMoments p [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  by_cases hj : j=i
  · subst j
    rw [ite_eq_left rfl]
    have he := inner_selfAdjoint_word (τ p) (C p) (C_selfAdjoint p) i [i]
    simpa [signalMoments, wordEval, variance, inner_self_eq_norm_sq_to_K] using he.symm
  · rw [ite_eq_right hj]; exact C_offDiagonal p i j hj
 theorem signalCumulants_centered (hp : 2 ≤ p) (i : Fin (p+1)) :
    cumulants (signalMoments p) [i] = 0 := by
  rw [cumulants_one _ (by simp [signalMoments]), C_centered p hp]
 theorem signalCumulants_covariance (hp : 2 ≤ p) (i j : Fin (p+1)) :
    cumulants (signalMoments p) [i,j] = if j=i then (variance p i : ℂ) else 0 := by
  rw [cumulants_two _ (by simp [signalMoments]), C_centered p hp, zero_mul, sub_zero, C_covariance]
 theorem variance_last_le_one (hp : 2 ≤ p) : variance p (Fin.last p) ≤ 1 := by
  have he := (C p (Fin.last p)).le_opNorm (τ p).vacuum
  rw [(τ p).norm_vacuum, mul_one, C_last] at he
  have hn := equidiscreteSignal_norm_le (B := Fin p) (N := Fin ((p+1)+(p+1))) p hp
  unfold variance
  rw [C_last]
  nlinarith [norm_nonneg (equidiscreteSignal p (τ p).vacuum)]
 theorem variance_castSucc (i : Fin p) : variance p i.castSucc = 1 := by
  have he := C_covariance p i.castSucc i.castSucc
  have ht := signal_option_moments p [some i,some i]
  simp only [List.map_cons, List.map_nil, optionFin_some, List.filterMap_cons, List.filterMap_nil,
    id_eq, fockMoments_two, ite_true] at ht
  simp at ht
  rw [ite_eq_left rfl, ht] at he
  exact_mod_cast he.symm
 theorem variance_le_one (hp : 2 ≤ p) (i : Fin (p+1)) : variance p i ≤ 1 := by
  induction i using Fin.lastCases with
  | last => exact variance_last_le_one p hp
  | cast i => rw [variance_castSucc]
end Model
end FiniteEntropySeparation

end

end OAI
