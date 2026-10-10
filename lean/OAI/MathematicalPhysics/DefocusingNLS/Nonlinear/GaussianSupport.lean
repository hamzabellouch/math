import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith

namespace OAI

/-!
# Supporting probability lemmas for stable defocusing NLS blowup

These lemmas formalize the measure and quantifier steps in the proof of
Corollary 1.2 of *Stable self-similar blowup for a supercritical defocusing
Schrödinger equation on the torus* (September 2026).
The independent head/tail argument uses Mathlib's
measure-theoretic independence theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DefocusingNLS

/-- If the expectation of a nonnegative random variable is below a threshold,
its strict sublevel set has positive probability. Applied to the squared tail
norm, this supplies the tail event in the Fourier support argument. -/
theorem positive_sublevel_of_lintegral_lt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ≥0∞} {c : ℝ≥0∞}
    (hmean : (∫⁻ ω, F ω ∂μ) < c) : 0 < μ {ω | F ω < c} := by
  by_contra hpos
  have hzero : μ {ω | F ω < c} = 0 := le_antisymm (le_of_not_gt hpos) bot_le
  have hbound : ∀ᵐ ω ∂μ, c ≤ F ω := by
    rw [ae_iff]
    simpa only [not_le] using hzero
  have : c ≤ ∫⁻ ω, F ω ∂μ := by
    calc
      c = ∫⁻ _ω : Ω, c ∂μ := by simp
      _ ≤ ∫⁻ ω, F ω ∂μ := lintegral_mono_ae hbound
  exact (not_le_of_gt hmean) this

section Probability

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
  {μ : Measure Ω} {X H : Ω → E} {f g : E} {r : ℝ}

/-- Independent positive-probability head and tail events put the full random
variable in a prescribed ball with positive probability. -/
theorem positive_ball_of_independent_head_tail
    (happrox : ‖f - g‖ < r / 3)
    (hhead : 0 < μ {ω | ‖H ω - g‖ < r / 3})
    (htail : 0 < μ {ω | ‖X ω - H ω‖ < r / 3})
    (hindep : IndepSet {ω | ‖H ω - g‖ < r / 3}
      {ω | ‖X ω - H ω‖ < r / 3} μ) :
    0 < μ (X ⁻¹' Metric.ball f r) := by
  have hpos : 0 < μ ({ω | ‖H ω - g‖ < r / 3} ∩
      {ω | ‖X ω - H ω‖ < r / 3}) := by
    rw [hindep.measure_inter_eq_mul]
    exact ENNReal.mul_pos hhead.ne' htail.ne'
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  intro ω hω
  change dist (X ω) f < r
  rw [dist_eq_norm]
  calc
    ‖X ω - f‖ = ‖(X ω - H ω) + (H ω - g) + (g - f)‖ := by
      congr 1
      abel
    _ ≤ ‖X ω - H ω‖ + ‖H ω - g‖ + ‖g - f‖ := norm_add₃_le
    _ < r / 3 + r / 3 + r / 3 := by
      rw [norm_sub_rev g f]
      exact add_lt_add (add_lt_add hω.2 hω.1) happrox
    _ = r := by ring

/-- Nonempty open sets have positive probability whenever the above head/tail
approximation can be made at every center and radius. This is the exact
measure-theoretic part of the Gaussian support argument. -/
theorem positive_open_of_head_tail
    (hsplit : ∀ (f : E) (r : ℝ), 0 < r →
      ∃ (H : Ω → E) (g : E), ‖f - g‖ < r / 3 ∧
        0 < μ {ω | ‖H ω - g‖ < r / 3} ∧
        0 < μ {ω | ‖X ω - H ω‖ < r / 3} ∧
        IndepSet {ω | ‖H ω - g‖ < r / 3}
          {ω | ‖X ω - H ω‖ < r / 3} μ)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < μ (X ⁻¹' U) := by
  obtain ⟨f, hf⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU f hf
  obtain ⟨H, g, happrox, hhead, htail, hindep⟩ := hsplit f r hr
  exact lt_of_lt_of_le
    (positive_ball_of_independent_head_tail happrox hhead htail hindep)
    (measure_mono (preimage_mono hball))

omit [NormedAddCommGroup E] in
/-- A positive-probability set of data incompatible with global continuation
rules out almost-sure global continuation. No measurability of the bad-data
predicate is needed for this implication. -/
theorem not_ae_of_positive_bad_set {B : Set E} {Good : E → Prop}
    (hB : 0 < μ (X ⁻¹' B)) (hbad : ∀ x ∈ B, ¬ Good x) :
    ¬ ∀ᵐ ω ∂μ, Good (X ω) := by
  intro hgood
  have hzero : μ {ω | ¬ Good (X ω)} = 0 := by
    simpa only [ae_iff] using hgood
  have hle : μ (X ⁻¹' B) ≤ μ {ω | ¬ Good (X ω)} :=
    measure_mono (fun ω hω => hbad (X ω) hω)
  rw [hzero] at hle
  exact (not_le_of_gt hB) hle

end Probability

/-- The fixed index supplied by the deterministic theorem refutes every finite
Gaussian regularity threshold, with the strict inequalities in the manuscript. -/
theorem no_universal_regularity_threshold {Global : ℝ → ℝ → Prop} {k : ℝ}
    (hk : 8 < k) (hfailure : ∀ α : ℝ, k + 6 < α → ¬ Global α k) :
    ¬ ∃ α₀ : ℝ, ∀ α : ℝ, α₀ < α →
      ∀ m : ℝ, 8 < m → m < α - 6 → Global α m := by
  rintro ⟨α₀, hglobal⟩
  let α := max α₀ (k + 6) + 1
  have hα₀ : α₀ < α := by
    dsimp [α]
    linarith [le_max_left α₀ (k + 6)]
  have hαk : k + 6 < α := by
    dsimp [α]
    linarith [le_max_right α₀ (k + 6)]
  exact hfailure α hαk (hglobal α hα₀ k hk (by linarith))

end DefocusingNLS

end OAI
