import OAI.Analysis.CircleDomains.Selection.JumpTollLowerBound
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

/-! Compactness for one new jump: both endpoints and a dust point collapse
together, and its limiting cost pays the dust toll. -/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem exists_shrinking_jump_limits
    (B : Set X) (hB : IsClosed B) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞)
    {τ : ℝ} (hτ : 0 < τ) (V : ℕ → Set X) (x y : ℕ → X)
    (hx : ∀n, x n ∈ V n) (hy : ∀n, y n ∈ V n)
    (hBmeet : ∀n, (V n ∩ B).Nonempty)
    (hdiam : Tendsto (fun n => diam (V n)) atTop (𝓝 0)) :
    ∃(s : ℕ → ℕ) (p : X) (A : ℝ≥0∞), StrictMono s ∧ p ∈ B ∧
      Tendsto (x ∘ s) atTop (𝓝 p) ∧ Tendsto (y ∘ s) atTop (𝓝 p) ∧
      Tendsto (fun n => fixedWidthJumpToll B m ρ τ (V (s n))) atTop (𝓝 A) ∧ m p ≤ A := by
  let v : ℕ → X × ℝ≥0∞ := fun n => (x n, fixedWidthJumpToll B m ρ τ (V n))
  obtain ⟨q, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (v n))
  have hxs : Tendsto (x ∘ s) atTop (𝓝 q.1) := (continuous_fst.tendsto q).comp hv
  have hcost : Tendsto (fun n => fixedWidthJumpToll B m ρ τ (V (s n))) atTop (𝓝 q.2) :=
    (continuous_snd.tendsto q).comp hv
  have hclose (z : ℕ → X) (hz : ∀n, z n ∈ V n) :
      Tendsto (fun n => dist (x (s n)) (z (s n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ (hdiam.comp hs.tendsto_atTop)
    intro n
    exact dist_le_diam_of_mem ((isCompact_univ : IsCompact (univ : Set X)).isBounded.subset (subset_univ (V (s n)))) (hx _) (hz _)
  choose b hb using hBmeet
  have hbV (n : ℕ) : b n ∈ V n := (hb n).1
  have hpB : q.1 ∈ B := hB.mem_of_tendsto (hxs.congr_dist (hclose b hbV))
    (Eventually.of_forall (fun n => (hb (s n)).2))
  exact ⟨s, q.1, q.2, hs, hpB, hxs, hxs.congr_dist (hclose y hy), hcost,
    limiting_fixedWidthJumpToll_ge B m ρ hτ hxs (fun n => hx (s n)) hpB hcost⟩

end CircleDomainRigidity

end

end OAI
