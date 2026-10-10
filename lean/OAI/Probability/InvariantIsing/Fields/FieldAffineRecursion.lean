import OAI.Probability.InvariantIsing.Fields.FieldSmoothFamily

namespace OAI

/-! The actual finite scalar log-cosh recursion with affine covariance
increments is a smooth field family on its strict covariance interval. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldLogCoshFamily (I : Set ℝ) : FieldSmoothFamily I where
  U := fun p => Real.log (Real.cosh p.2)
  X := fun p => Real.tanh p.2
  XX := fun p => 1 / (Real.cosh p.2) ^ 2
  T := fun _ => 0
  KX := 1
  KXX := 1
  KT := 0
  mU := by fun_prop
  mX := by
    have ht : Measurable (fun x : ℝ => Real.tanh x) := by
      simp only [Real.tanh_eq]
      fun_prop
    exact ht.comp measurable_snd
  mXX := by fun_prop
  mT := measurable_const
  bX := fun p => field_abs_tanh_le_one p.2
  bXX := fun p => field_tanh_second_bound p.2
  bT := fun _ _ => by simp
  derivative := fun p _ => by
    have h : HasDerivAt (fun x => Real.log (Real.cosh x)) (Real.tanh p.2) p.2 := by
      simpa only [Real.tanh_eq_sinh_div_cosh] using
        (Real.hasDerivAt_cosh p.2).log (Real.cosh_pos p.2).ne'
    have hs : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
      hasFDerivAt_snd
    convert h.hasFDerivAt.comp p hs using 1
    · rfl
    · apply ContinuousLinearMap.ext
      intro q
      simp [pairLinear, mul_comm]
  spatial := fun _ y => by
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh y).log (Real.cosh_pos y).ne'
  second := fun _ y => field_hasDerivAt_tanh y

structure FieldAffineStep where
  base : ℝ
  slope : ℝ
  exponent : ℝ

def fieldAffineValue : List FieldAffineStep → ℝ × ℝ → ℝ
  | [], p => Real.log (Real.cosh p.2)
  | av :: L, p => gaussianTransform (av.base + av.slope * p.1) av.exponent
      (fun y => fieldAffineValue L (p.1, y)) p.2

def fieldAffineFamily (I : Set ℝ) (hI : IsOpen I) :
    (L : List FieldAffineStep) →
      (∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) → FieldSmoothFamily I
  | [], _ => fieldLogCoshFamily I
  | av :: L, hL =>
      (fieldAffineFamily I hI L (fun bv hb => hL bv (List.mem_cons_of_mem av hb))).transform
        hI av.base av.slope av.exponent (hL av List.mem_cons_self)

theorem fieldAffineFamily_value (I : Set ℝ) (hI : IsOpen I) (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t) :
    (fieldAffineFamily I hI L hL).U = fieldAffineValue L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    funext p
    simp only [fieldAffineFamily, FieldSmoothFamily.transform, FieldSmoothFamily.value,
      fieldAffineValue]
    rw [ih]

theorem fieldAffineValue_hasFDerivAt (I : Set ℝ) (hI : IsOpen I)
    (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, 0 < av.base + av.slope * t)
    (p : ℝ × ℝ) (hp : p.1 ∈ I) :
    HasFDerivAt (fieldAffineValue L)
      (pairLinear ((fieldAffineFamily I hI L hL).T p)
        ((fieldAffineFamily I hI L hL).X p)) p := by
  rw [← fieldAffineFamily_value I hI L hL]
  exact (fieldAffineFamily I hI L hL).derivative p hp

end InvariantIsing

end

end OAI
