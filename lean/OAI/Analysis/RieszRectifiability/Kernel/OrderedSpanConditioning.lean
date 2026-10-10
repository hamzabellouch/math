import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.SpanCoefficientControl

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped BigOperators

def OrderedSpanSeparated {d : ℕ} : (n : ℕ) → (Fin n → Ambient d) → ℝ → Prop
  | 0, _, _ => True
  | n + 1, v, r => OrderedSpanSeparated n (Fin.init v) r ∧
      r ≤ infDist (v (Fin.last n)) (Submodule.span ℝ (range (Fin.init v)) : Set (Ambient d))

def spanConditionConstant (M r : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => spanConditionConstant M r n * (1 + M / r) + 1 / r

theorem spanConditionConstant_nonneg (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r) (n : ℕ) :
    0 ≤ spanConditionConstant M r n := by
  induction n with
  | zero => simp [spanConditionConstant]
  | succ n ih =>
    simp only [spanConditionConstant]
    positivity

theorem ordered_span_coefficient_bound {n d : ℕ}
    (v : Fin n → Ambient d) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r)
    (hv : ∀ i, ‖v i‖ ≤ M) (hsep : OrderedSpanSeparated n v r) (t : Fin n → ℝ) :
    (∑ i, |t i|) ≤ spanConditionConstant M r n * ‖∑ i, t i • v i‖ := by
  induction n with
  | zero => simp [spanConditionConstant]
  | succ n ih =>
    have hp : ∀ s : Fin n → ℝ, (∑ i, |s i|) ≤
        spanConditionConstant M r n * ‖∑ i, s i • Fin.init v i‖ :=
      fun s => ih (Fin.init v) (fun i => hv i.castSucc) hsep.1 s
    have h := coordinate_bound_extend (Fin.init v) (v (Fin.last n))
      (spanConditionConstant M r n) M r (spanConditionConstant_nonneg M r hM hr n)
      (hv (Fin.last n)) hr hsep.2 hp (Fin.init t) (t (Fin.last n))
    simpa only [spanConditionConstant, Fin.sum_univ_castSucc, Fin.init] using! h

theorem linearIndependent_of_coordinate_bound {n d : ℕ}
    (v : Fin n → Ambient d) (C : ℝ)
    (hbound : ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤ C * ‖∑ i, t i • v i‖) :
    LinearIndependent ℝ v := by
  apply Fintype.linearIndependent_iff.mpr
  intro t ht i
  have h := hbound t
  rw [ht, norm_zero, mul_zero] at h
  have hi : |t i| ≤ ∑ j, |t j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
  exact abs_eq_zero.mp (le_antisymm (hi.trans h) (abs_nonneg _))

theorem ordered_span_linearIndependent {n d : ℕ}
    (v : Fin n → Ambient d) (M r : ℝ) (hM : 0 ≤ M) (hr : 0 < r)
    (hv : ∀ i, ‖v i‖ ≤ M) (hsep : OrderedSpanSeparated n v r) :
    LinearIndependent ℝ v :=
  linearIndependent_of_coordinate_bound v (spanConditionConstant M r n)
    (ordered_span_coefficient_bound v M r hM hr hv hsep)

end

end RieszRectifiability

end OAI
