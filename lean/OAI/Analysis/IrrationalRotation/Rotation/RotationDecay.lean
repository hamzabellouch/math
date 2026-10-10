import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section

open scoped BigOperators
open Filter Finset

namespace InvariantProjection.RotationDecay

variable {X : Type*}

def truncatedLog (f : X → ℝ) (M : ℝ) (x : X) : ℝ :=
  Real.log (max (f x) (Real.exp (-M)))

def orbitProduct (σ : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  ∏ k ∈ range n, f (σ^[k] x)

lemma le_exp_truncatedLog (f : X → ℝ) (M : ℝ) (x : X) :
    f x ≤ Real.exp (truncatedLog f M x) := by
  rw [truncatedLog, Real.exp_log (lt_of_lt_of_le (Real.exp_pos (-M)) (le_max_right _ _))]
  exact le_max_left _ _

lemma orbitProduct_nonneg {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (n : ℕ) (x : X) :
    0 ≤ orbitProduct σ f n x := by
  exact prod_nonneg fun k _ => hf (σ^[k] x)

lemma orbitProduct_le_exp_sum_truncatedLog {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M : ℝ) (n : ℕ) (x : X) :
    orbitProduct σ f n x ≤
      Real.exp (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) := by
  rw [Real.exp_sum]
  exact prod_le_prod₀ (fun k _ => hf (σ^[k] x))
    (fun k _ => le_exp_truncatedLog f M (σ^[k] x))

lemma orbitProduct_le_exp_of_sum_le {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a : ℝ) (n : ℕ) (x : X)
    (h : (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) ≤ -a * n) :
    orbitProduct σ f n x ≤ Real.exp (-a * n) :=
  (orbitProduct_le_exp_sum_truncatedLog hf M n x).trans (Real.exp_le_exp.mpr h)

lemma orbitProduct_le_exp_of_average_le {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a : ℝ) {n : ℕ} (hn : 0 < n) (x : X)
    (h : birkhoffAverage ℝ σ (truncatedLog f M) n x ≤ -a) :
    orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  apply orbitProduct_le_exp_of_sum_le hf M a n x
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  change (n : ℝ)⁻¹ * (∑ k ∈ range n, truncatedLog f M (σ^[k] x)) ≤ -a at h
  have h' := mul_le_mul_of_nonneg_left h hn'.le
  simpa [← mul_assoc, mul_inv_cancel₀ hn'.ne', mul_comm (n : ℝ) (-a)] using h'

lemma eventually_orbitProduct_le_exp {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x) (M a I : ℝ) (ha : 0 < a) (hI : I < -2 * a)
    (havg : TendstoUniformly
      (fun n x => birkhoffAverage ℝ σ (truncatedLog f M) n x)
      (fun _ => I) atTop) :
    ∀ᶠ n in atTop, ∀ x, orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  have hclose := (Metric.tendstoUniformly_iff.mp havg) a ha
  filter_upwards [hclose, eventually_gt_atTop 0] with n hn hnpos
  intro x
  apply orbitProduct_le_exp_of_average_le hf M a hnpos x
  have hx := hn x
  rw [Real.dist_eq] at hx
  have hx' := (abs_lt.mp hx).1
  linarith

theorem all_rates_orbitProduct_decay {σ : X → X} {f : X → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmean : ∀ a : ℝ, 0 < a → ∃ M I : ℝ, I < -2 * a ∧
      TendstoUniformly
        (fun n x => birkhoffAverage ℝ σ (truncatedLog f M) n x)
        (fun _ => I) atTop) :
    ∀ a : ℝ, 0 < a →
      ∀ᶠ n in atTop, ∀ x, orbitProduct σ f n x ≤ Real.exp (-a * n) := by
  intro a ha
  obtain ⟨M, I, hI, havg⟩ := hmean a ha
  exact eventually_orbitProduct_le_exp hf M a I ha hI havg

end InvariantProjection.RotationDecay

end

end OAI
