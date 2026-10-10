import OAI.NumberTheory.JointDickman.Counting.PeriodicAverages

namespace OAI

/-! # Real moments of a fixed finite-period function -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem real_periodic_moment_tendsto {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (f n)^k) / (N : ℝ))
      atTop (nhds ((∑ a : ZMod q, (f a)^k) / (q : ℝ))) := by
  have h := periodicAverage_tendsto (fun a => (((f a)^k : ℝ) : ℂ))
  have hr := Complex.continuous_re.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, periodicAverage, residueMean,
    Complex.div_natCast_re, Complex.re_sum, Complex.ofReal_re] using hr

end JointDickman

end OAI
