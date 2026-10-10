import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceScaleExtraction
import Mathlib.Topology.MetricSpace.Basic

namespace OAI

/-! # Removing the basepoint from stabilized labels -/

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- A label already stable in scale is independent of the center once
nearby-center comparisons hold along all diverging scales. -/
theorem stable_label_independent_of_center
    {P X L : Type*} [PseudoMetricSpace X]
    (label : P → X → ℝ → L) {r₀ t η : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hstable : ∀ p x r, r₀ ≤ r → label p x r = label p x r₀)
    (hcompare : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ p x y, (∀ n, dist x y ≤ η * scale n) →
        ∀ᶠ n in atTop, label p x (scale n) = label p y (t * scale n)) :
    ∀ p x y, label p x r₀ = label p y r₀ := by
  intro p x y
  let B := max 1 (max t⁻¹ (dist x y / η))
  let scale := fun n : ℕ => (n : ℝ) + B
  have hlow n : B ≤ scale n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hgrow : Tendsto scale atTop atTop := tendsto_atTop_add_const_right _ B
    tendsto_natCast_atTop_atTop
  have hstrict : StrictMono scale := by
    intro i j hij
    have hh : (i : ℝ) < j := by exact_mod_cast hij
    dsimp only [scale]
    linarith only [hh]
  have h1 n : 1 ≤ scale n := (le_max_left _ _).trans (hlow n)
  have ht1 n : 1 ≤ t * scale n := by
    have hh : t⁻¹ ≤ scale n := ((le_max_left _ _).trans (le_max_right _ _)).trans (hlow n)
    have hh' := mul_le_mul_of_nonneg_left hh ht.le
    simpa only [mul_inv_cancel₀ ht.ne'] using hh'
  have hd n : dist x y ≤ η * scale n := by
    have hh : dist x y / η ≤ scale n :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans (hlow n)
    exact (div_le_iff₀ hη).mp hh |>.trans_eq (mul_comm _ _)
  have he := hcompare scale hgrow hstrict h1 ht1 p x y hd
  have hsmall : Tendsto (fun n => t * scale n) atTop atTop := hgrow.const_mul_atTop ht
  obtain ⟨n, hn, hn', heq⟩ := ((hgrow.eventually_ge_atTop r₀).and
    ((hsmall.eventually_ge_atTop r₀).and he)).exists
  exact (hstable p x _ hn).symm.trans (heq.trans (hstable p y _ hn'))

/-- Uniform control in a scale parameter follows from tests along arbitrary
strictly increasing scales, with the same local-distance constraint. -/
theorem uniform_local_norm_bound_of_sequences
    {P X W : Type*} [PseudoMetricSpace X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (error : P → X → X → W) {t η : ℝ} (ht : 0 < t)
    (hseq : ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ t * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → X), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      Tendsto (fun n => (scale n)⁻¹ • error (p n) (x n) (y n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 1 ≤ R ∧ ∀ p x y r,
      R ≤ r → dist x y ≤ η * r → ‖error p x y‖ ≤ ε * r := by
  classical
  intro ε hε
  by_contra h
  push Not at h
  have hex (n : ℕ) := h (max 1 (max (n : ℝ) t⁻¹)) (le_max_left _ _)
  choose p x y r hr hd herr using hex
  have hr1 n : 1 ≤ r n := (le_max_left _ _).trans (hr n)
  have htr n : 1 ≤ t * r n := by
    have hh : t⁻¹ ≤ r n := ((le_max_right _ _).trans (le_max_right _ _)).trans (hr n)
    simpa only [mul_inv_cancel₀ ht.ne'] using mul_le_mul_of_nonneg_left hh ht.le
  have hrgrow : Tendsto r atTop atTop := tendsto_atTop_mono
    (fun n => ((le_max_left _ _).trans (le_max_right _ _)).trans (hr n))
    tendsto_natCast_atTop_atTop
  obtain ⟨u, hu, hru, _⟩ := exists_strictMono_scale_subsequence r hrgrow
  have hh := hseq (r ∘ u) (hrgrow.comp hu.tendsto_atTop) hru
    (fun n => hr1 (u n)) (fun n => htr (u n)) (p ∘ u) (x ∘ u) (y ∘ u)
    (fun n => hd (u n))
  obtain ⟨n, hn⟩ := ((tendsto_zero_iff_norm_tendsto_zero.mp hh).eventually
    (gt_mem_nhds hε)).exists
  have hp : 0 < r (u n) := zero_lt_one.trans_le (hr1 (u n))
  have hn' : ‖error (p (u n)) (x (u n)) (y (u n))‖ < ε * r (u n) := by
    have hnorm : ‖error (p (u n)) (x (u n)) (y (u n))‖ / r (u n) < ε := by
      simpa only [Function.comp_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hp), inv_mul_eq_div] using hn
    exact (div_lt_iff₀ hp).mp hnorm
  exact (not_lt_of_ge (herr (u n)).le) hn'

end PolycyclicRecognition

end OAI
