import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OAI

/-! # Rouché's theorem on the spectral counting rectangle

The rectangle specialization of Rouché's theorem is formulated as a proposition.
See L. V. Ahlfors, *Complex Analysis*, third edition, McGraw-Hill, 1979,
Chapter 4, §5.2, p. 153, Corollary following Theorem 18.
The zero count uses analytic vanishing orders, including multiplicity.
-/

open Set

namespace DefocusingNLS

def countingRectangle (V : ℝ) : Set ℂ :=
  {z | -(1 / 32 : ℝ) < z.re ∧ z.re < 8 ∧ -V < z.im ∧ z.im < V}

def closedCountingRectangle (V : ℝ) : Set ℂ :=
  {z | -(1 / 32 : ℝ) ≤ z.re ∧ z.re ≤ 8 ∧ -V ≤ z.im ∧ z.im ≤ V}

def countingRectangleBoundary (V : ℝ) : Set ℂ :=
  closedCountingRectangle V \ countingRectangle V

noncomputable def rectangleZeroCount (V : ℝ) (f : ℂ → ℂ) : ℕ∞ :=
  ∑' z : countingRectangle V, analyticOrderAt f z.1

/-- Ahlfors's Rouché corollary, specialized to the one family of rectangles used
for the spectral count. No spectral conclusion is included in this input. -/
def RectangleRouche : Prop :=
  ∀ (V : ℝ), 0 < V → ∀ (f g : ℂ → ℂ),
    AnalyticOnNhd ℂ f (closedCountingRectangle V) →
    AnalyticOnNhd ℂ g (closedCountingRectangle V) →
    (∀ z ∈ countingRectangleBoundary V, ‖g z - f z‖ < ‖f z‖) →
    rectangleZeroCount V f = rectangleZeroCount V g

theorem isOpen_countingRectangle (V : ℝ) : IsOpen (countingRectangle V) := by
  convert isOpen_Ioo.reProdIm (isOpen_Ioo (a := -V) (b := V)) using 1
  ext z
  simp only [countingRectangle, Complex.mem_reProdIm, mem_ofPred_eq, mem_Ioo]
  tauto

theorem isCompact_closedCountingRectangle (V : ℝ) : IsCompact (closedCountingRectangle V) := by
  convert (isCompact_Icc (a := -(1 / 32 : ℝ)) (b := 8)).reProdIm
    (isCompact_Icc (a := -V) (b := V)) using 1
  ext z
  simp only [closedCountingRectangle, Complex.mem_reProdIm, mem_ofPred_eq, mem_Icc]
  tauto

theorem isCompact_countingRectangleBoundary (V : ℝ) :
    IsCompact (countingRectangleBoundary V) :=
  (isCompact_closedCountingRectangle V).diff (isOpen_countingRectangle V)

theorem mem_countingRectangleBoundary_iff (V : ℝ) (z : ℂ) :
    z ∈ countingRectangleBoundary V ↔
      z ∈ closedCountingRectangle V ∧
        (z.re = -(1 / 32 : ℝ) ∨ z.re = 8 ∨ z.im = -V ∨ z.im = V) := by
  simp only [countingRectangleBoundary, closedCountingRectangle, countingRectangle,
    mem_sdiff, mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    by_contra h
    push Not at h
    exact hn ⟨lt_of_le_of_ne hz.1 h.1.symm, lt_of_le_of_ne hz.2.1 h.2.1,
      lt_of_le_of_ne hz.2.2.1 h.2.2.1.symm, lt_of_le_of_ne hz.2.2.2 h.2.2.2⟩
  · rintro ⟨hz, he⟩
    refine ⟨hz, ?_⟩
    rintro ⟨ha, hb, hc, hd⟩
    rcases he with he | he | he | he <;> linarith

end DefocusingNLS

end OAI
