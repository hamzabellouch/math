import OAI.Probability.SATComputability.FinitePushforward
import Mathlib.MeasureTheory.Integral.Pi

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators Classical

theorem product_indicator_eq {I : Type*} [Fintype I] {X : I → Type*}
    (x y : ∀ i, X i) :
    (if x = y then (1 : ℝ) else 0) = ∏ i, if x i = y i then 1 else 0 := by
  by_cases h : x = y
  · simp [h]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h]
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm

theorem finitePushforward_pi {I : Type*} [Fintype I] [DecidableEq I]
    {X Y : I → Type*} [∀ i, MeasurableSpace (X i)] [∀ i, Fintype (Y i)]
    [∀ i, MeasurableSpace (Y i)] [∀ i, MeasurableSingletonClass (Y i)]
    (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (g : ∀ i, X i → Y i) (hg : ∀ i, Measurable (g i)) :
    finitePushforward (Measure.pi μ) (fun x i => g i (x i))
        (Measurable.of_eval (fun i => (hg i).comp (measurable_pi_apply i))) =
      FiniteLaw.pi (fun i => finitePushforward (μ i) (g i) (hg i)) := by
  classical
  let : DecidableEq ((i : I) → Y i) := Classical.decEq _
  apply FiniteLaw.weights_ext
  intro y
  simp only [finitePushforward, FiniteLaw.pi]
  have he (x : ∀ i, X i) :
      (if (fun i => g i (x i)) = y then (1 : ℝ) else 0) =
        ∏ i, if g i (x i) = y i then (1 : ℝ) else 0 := by
    by_cases h : (fun i => g i (x i)) = y
    · have hh (i : I) := congrFun h i
      simp [hh]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ := Function.ne_iff.mp h
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)).symm
  exact (integral_congr_ae (ae_of_all (Measure.pi μ) he)).trans
    (integral_fintype_prod_eq_prod (μ := μ) (fun i x => if g i x = y i then (1 : ℝ) else 0))

theorem finitePushforward_congr {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (f g : X → Y)
    (hf : Measurable f) (hg : Measurable g) (he : ∀ x, f x = g x) :
    finitePushforward μ f hf = finitePushforward μ g hg := by
  cases funext he
  rfl

theorem finiteLaw_eq_of_expect {Y : Type*} [Fintype Y] (P Q : FiniteLaw Y)
    (h : ∀ f, P.expect f = Q.expect f) : P = Q := by
  apply FiniteLaw.weights_ext
  intro y
  simpa only [FiniteLaw.expect, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h (fun x => if x = y then 1 else 0)

end FixedClauseThreshold.Computability

end OAI
