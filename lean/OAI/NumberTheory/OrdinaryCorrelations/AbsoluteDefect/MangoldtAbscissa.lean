import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Complete

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

namespace OrdinaryLogDerivative
open LSeries MeasureTheory

lemma mangoldt_abscissa {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) :
    LSeries.abscissaOfAbsConv (mangoldtTwist f) ≤ (1:ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro s hs
  exact mangoldt_summable hf hs

lemma continuousOn_horizontal {f : ℕ → ℂ} {σ : ℝ}
    (hf : LSeries.abscissaOfAbsConv f ≤ (σ: EReal)) (s : ℂ) (hs : σ < s.re) :
    ContinuousOn (fun x : ℝ => LSeries f (s + x)) (Set.Ici 0) := by
  intro x hx
  have hab : LSeries.abscissaOfAbsConv f < ((s+x).re: EReal) :=
    lt_of_le_of_lt hf (by
      apply EReal.coe_lt_coe_iff.mpr
      simp only [Complex.add_re,Complex.ofReal_re]
      linarith [show 0≤x from hx])
  have hp : ContinuousAt (fun y : ℝ => s+(y:ℂ)) x := by fun_prop
  exact (ContinuousAt.comp (g := fun z : ℂ => LSeries f z)
    (f := fun y : ℝ => s+(y:ℂ)) (LSeries_hasDerivAt hab).continuousAt hp).continuousWithinAt

lemma horizontal_hasDerivAt {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hm : Complete f) (s : ℂ) {x : ℝ} (hs : 1 < (s+x).re) :
    HasDerivAt (fun x : ℝ => LSeries f (s+x))
      (-(LSeries (mangoldtTwist f) (s+x)*LSeries f (s+x))) x := by
  have hab : LSeries.abscissaOfAbsConv f < ((s+x).re: EReal) :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => hf n⟩)
      (by exact_mod_cast hs)
  have hd := (LSeries_hasDerivAt hab).differentiableAt.hasDerivAt
  rw [LSeries_derivative_product hf hm hs] at hd
  have hp := (hasDerivAt_id (x:ℂ)).const_add s
  simpa only [Function.comp_def,id_eq,mul_one] using (hd.comp (x:ℂ) hp).comp_ofReal

theorem horizontal_identity {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hm : Complete f) (s : ℂ) (hs : 1 < s.re) {a : ℝ} (ha : 0≤a) :
    LSeries f s = LSeries f (s+a) +
      ∫ x : ℝ in 0..a, LSeries (mangoldtTwist f) (s+x)*LSeries f (s+x) := by
  have hfcont := continuousOn_horizontal
    (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hf n⟩) s hs
  have hgcont := continuousOn_horizontal (mangoldt_abscissa hf) s hs
  have hcont := (hgcont.mul hfcont).mono (show Set.uIcc 0 a ⊆ Set.Ici 0 by
    rw [Set.uIcc_of_le ha]; exact fun x hx => hx.1)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f:=fun x : ℝ => LSeries f (s+x))
    (f':=fun x : ℝ => -(LSeries (mangoldtTwist f) (s+x)*LSeries f (s+x)))
    (fun x hx => horizontal_hasDerivAt hf hm s (by
      have hx0 : 0≤x := (Set.uIcc_of_le ha ▸ hx).1
      simp only [Complex.add_re,Complex.ofReal_re]
      linarith)) hcont.neg.intervalIntegrable
  rw [intervalIntegral.integral_neg] at hi
  simp only [Complex.ofReal_zero,add_zero] at hi
  linear_combination hi

end OrdinaryLogDerivative

end

end OAI
