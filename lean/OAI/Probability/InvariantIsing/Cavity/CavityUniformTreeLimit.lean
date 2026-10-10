import OAI.Probability.InvariantIsing.Cavity.CavityCutoffLimit
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace OAI

/-! A limit valid for every sequence of labeled trees is uniform in the
tree choice and survives averaging over the original cascade law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_uniform_zero_of_all_selections {X : ℕ → Type*} [∀ n, Nonempty (X n)]
    (f : (n : ℕ) → X n → ℝ)
    (h : ∀ x : (n : ℕ) → X n, Tendsto (fun n => f n (x n)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x, |f n x| < ε := by
  classical
  intro ε hε
  let x : (n : ℕ) → X n := fun n =>
    if hn : ∃ x, ε ≤ |f n x| then Classical.choose hn else Classical.choice inferInstance
  have hx := (h x).eventually (Metric.ball_mem_nhds 0 hε)
  filter_upwards [hx] with n hn
  rw [Real.dist_eq,sub_zero] at hn
  intro y
  by_contra hy
  have he : ∃ y, ε ≤ |f n y| := ⟨y, le_of_not_gt hy⟩
  have hb : ε ≤ |f n (x n)| := by
    dsimp only [x]
    rw [dite_eq_left he]
    exact Classical.choose_spec he
  linarith

lemma cavity_average_zero_of_all_selections {X : ℕ → Type*}
    [∀ n, MeasurableSpace (X n)] [∀ n, Nonempty (X n)]
    (P : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (P n)]
    (f : (n : ℕ) → X n → ℝ)
    (h : ∀ x : (n : ℕ) → X n, Tendsto (fun n => f n (x n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ∂P n) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavity_uniform_zero_of_all_selections f h (ε/2) (by positivity)] with n hn
  have hh := norm_integral_le_of_norm_le_const (μ := P n) (f := f n)
    (C := ε/2) (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using (hn x).le)
  rw [Real.dist_eq,sub_zero]
  have hb : |∫ x, f n x ∂P n| ≤ ε/2 := by
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh
  exact hb.trans_lt (by linarith)

end InvariantIsing

end

end OAI
