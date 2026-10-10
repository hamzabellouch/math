import Mathlib

namespace OAI

open scoped ENNReal
noncomputable section

namespace TraceReconstruction

abbrev Word (n : ℕ) := Fin n → Bool
abbrev Mask (n : ℕ) := Fin n → Bool
abbrev Trace := List Bool

/-- `true` retains the bit. The observer gets only the resulting list. -/
def traceOfMask {n : ℕ} (x : Word n) (a : Mask n) : Trace :=
  ((List.finRange n).filter fun i => a i).map x

/-- The deletion-mask probability, with deletion probability `q`. -/
def maskWeight {n : ℕ} (q : ℝ) (a : Mask n) : ℝ :=
  ∏ i, if a i then 1 - q else q

/-- Law of a single complete trace. -/
def traceMass {n : ℕ} (q : ℝ) (x : Word n) (w : Trace) : ℝ :=
  ∑ a : Mask n, if traceOfMask x a = w then maskWeight q a else 0

/-- All possible complete outputs from length-n inputs, with lengths included. -/
def traceSpace (n : ℕ) : Finset Trace :=
  Finset.univ.biUnion fun k : Fin (n + 1) =>
    Finset.univ.image fun x : Word k.val => List.ofFn x

/-- 1/2 sum of absolute differences, on the full finite output space. -/
def traceTV {n : ℕ} (q : ℝ) (x y : Word n) : ℝ :=
  (1 / 2 : ℝ) * ∑ w ∈ traceSpace n, |traceMass q x w - traceMass q y w|

/-- The estimator may depend arbitrarily on n, q and every complete sample.
    Its value is its conditional probability of reporting the given input. -/
def IsEstimator {n m : ℕ} (A : (Fin m → Trace) → Word n → ℝ) : Prop :=
  (∀ z x, 0 ≤ A z x) ∧ (∀ z, ∑ x : Word n, A z x = 1)

/-- Independent masks generate independent complete traces; no retained
    positions, boundaries or other latent variables are revealed to A. -/
def reconstructionSuccess {n m : ℕ} (q : ℝ)
    (A : (Fin m → Trace) → Word n → ℝ) (x : Word n) : ℝ :=
  ∑ a : Fin m → Mask n,
    (∏ j, maskWeight q (a j)) * A (fun j => traceOfMask x (a j)) x

def SufficientBudget (n : ℕ) (q s : ℝ) (m : ℕ) : Prop :=
  ∃ A : (Fin m → Trace) → Word n → ℝ,
    IsEstimator A ∧ ∀ x, s ≤ reconstructionSuccess q A x

/-- Natural fixed sample budget; infimum of the empty set is infinity. -/
noncomputable def sampleComplexity (n : ℕ) (q s : ℝ) : ℝ≥0∞ :=
  sInf {t | ∃ m : ℕ, SufficientBudget n q s m ∧ t = (m : ℝ≥0∞)}

/-- The real infimum is a minimum for n>0 (a nonempty finite set). -/
noncomputable def minTraceTV (n : ℕ) (q : ℝ) : ℝ :=
  sInf {t | ∃ x y : Word n, x ≠ y ∧ t = traceTV q x y}

open Filter
open scoped Topology Classical ENNReal

theorem quantitative_sample_lower_bound
    (s c : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (hc : c ∈ Set.Ioo 0 (1 / (4 * Real.log 2)))
    (n : ℕ → ℕ) (q : ℕ → ℝ)
    (hn : Tendsto n atTop atTop)
    (hq : ∀ k, q k ∈ Set.Ioo 0 1)
    (hscale : Tendsto (fun k => (q k) ^ 3 * Real.log (n k)) atTop atTop) :
    ∀ᶠ k in atTop,
      ENNReal.ofReal ((n k : ℝ) ^ (c * Real.log ((q k) ^ 3 * Real.log (n k)))) ≤
        sampleComplexity (n k) (q k) s := by
  sorry

theorem superpolynomial_one_trace
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ C * minTraceTV n q) atTop (𝓝 0) := by
  sorry

theorem superpolynomial_sample_complexity
    (q : ℝ) (hq : q ∈ Set.Ioo 0 1) (s : ℝ) (hs : s ∈ Set.Ioc 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ => sampleComplexity n q s / ENNReal.ofReal ((n : ℝ) ^ C))
      atTop (𝓝 ⊤) := by
  sorry

end TraceReconstruction

end

end OAI
