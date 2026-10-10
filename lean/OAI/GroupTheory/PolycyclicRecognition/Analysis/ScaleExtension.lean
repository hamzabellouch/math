import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential

namespace OAI

/-! # Extending data from a strictly increasing sequence of scales

No regularity is imposed between the sampled scales. This bridge permits the
uniform real-scale estimates to be applied to the original sequence data.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

/-- Extend the data by a fixed value outside the sampled scales. -/
def extendOnScales {α : Type*} (r : ℕ → ℝ) (f : ℕ → α) (z : α) (t : ℝ) : α := by
  classical
  exact if h : ∃ n, r n = t then f h.choose else z

theorem extendOnScales_apply {α : Type*} {r : ℕ → ℝ} (hr : StrictMono r)
    (f : ℕ → α) (z : α) (n : ℕ) : extendOnScales r f z (r n) = f n := by
  classical
  unfold extendOnScales
  split_ifs with h
  · exact congrArg f (hr.injective h.choose_spec)
  · exact False.elim (h ⟨n, rfl⟩)

/-- Eventually true assertions on the indices hold at every sufficiently
large scale in the range; off that range the fixed default is used. -/
theorem eventually_extendOnScales {α : Type*} {r : ℕ → ℝ} (hr : StrictMono r)
    (f : ℕ → α) (z : α) (P : ℝ → α → Prop)
    (hz : ∀ t, P t z) (hf : ∀ᶠ n in atTop, P (r n) (f n)) :
    ∀ᶠ t in atTop, P t (extendOnScales r f z t) := by
  classical
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  filter_upwards [eventually_gt_atTop (r N)] with t ht
  unfold extendOnScales
  split_ifs with h
  · have hn : N ≤ h.choose := by
      by_contra hn
      have hlt : h.choose < N := Nat.lt_of_not_ge hn
      have hh := hr hlt
      rw [h.choose_spec] at hh
      exact (not_lt_of_ge ht.le) hh
    simpa only [h.choose_spec] using hN h.choose hn
  · exact hz t

theorem tendsto_extendOnScales {α : Type*} [TopologicalSpace α] {r : ℕ → ℝ}
    (hr : StrictMono r) {f : ℕ → α} {z : α} (hf : Tendsto f atTop (𝓝 z)) :
    Tendsto (extendOnScales r f z) atTop (𝓝 z) := by
  apply tendsto_def.2
  intro U hU
  exact eventually_extendOnScales hr f z (fun _ x => x ∈ U)
    (fun _ => mem_of_mem_nhds hU) (hf.eventually hU)

end PolycyclicRecognition

end

end OAI
