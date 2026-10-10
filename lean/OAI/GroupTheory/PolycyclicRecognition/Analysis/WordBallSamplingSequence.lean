import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordBallLeftShift
import OAI.GroupTheory.PolycyclicRecognition.Analysis.EventualSupportedSampling

namespace OAI

/-! # Selecting actual bounded chart maps at eventual sampling scales -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory Filter Metric
open scoped Manifold Topology

/-- The geometric witnesses can be selected along a sequence together with
continuous compact-ball chart maps. Early indices impose no conditions. -/
theorem exists_wordBall_sampling_sequence
    {L E G N : Type*} [LieRing L] [LieAlgebra ℝ L]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace G] [ChartedSpace E G] [Group G]
    [LieGroup (𝓘(ℝ, E)) ⊤ G] [IsTopologicalGroup G]
    [MeasurableSpace N] [Nonempty N]
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G)
    {d : ℕ} (source target : ℕ → Basis (Fin d) ℝ L)
    {R S : ℝ} (hS : 0 ≤ S)
    (P : ℕ → N → G → ProbabilityMeasure N → Prop)
    (hP : ∀ᶠ n in atTop, ∃ (u : N) (k : G) (ν : ProbabilityMeasure N),
      P n u k ν ∧ ∀ z : Fin d → ℝ, ‖z‖ ≤ R →
        ‖wordChartLeftShift e chart (source n) (target n) k z‖ ≤ S) :
    ∃ (u : ℕ → N) (k : ℕ → G) (ν : ℕ → ProbabilityMeasure N)
      (φ : ℕ → C(closedBall (0 : Fin d → ℝ) R, closedBall (0 : Fin d → ℝ) S)),
      ∀ᶠ n in atTop, P n (u n) (k n) (ν n) ∧ ∀ z,
        (φ n z : Fin d → ℝ) = wordChartLeftShift e chart (source n) (target n) (k n) z := by
  classical
  let Z := C(closedBall (0 : Fin d → ℝ) R, closedBall (0 : Fin d → ℝ) S)
  let : Nonempty Z := ⟨ContinuousMap.const _ ⟨0, mem_closedBall_self hS⟩⟩
  let : Nonempty (ProbabilityMeasure N) :=
    ⟨⟨Measure.dirac (Classical.choice (inferInstance : Nonempty N)), inferInstance⟩⟩
  let Q := fun n (v : N × G × ProbabilityMeasure N × Z) =>
    P n v.1 v.2.1 v.2.2.1 ∧ ∀ z,
      (v.2.2.2 z : Fin d → ℝ) = wordChartLeftShift e chart (source n) (target n) v.2.1 z
  have hQ : ∀ᶠ n in atTop, ∃ v, Q n v := by
    filter_upwards [hP] with n hn
    obtain ⟨u, k, ν, hp, hbound⟩ := hn
    exact ⟨⟨u, k, ν, wordBallLeftShift e chart (source n) (target n) k R S hbound⟩,
      hp, fun _ => rfl⟩
  obtain ⟨v, hv⟩ := exists_eventually_chosen_sequence Q hQ
  exact ⟨(fun n => (v n).1), (fun n => (v n).2.1), (fun n => (v n).2.2.1),
    (fun n => (v n).2.2.2), hv⟩

end PolycyclicRecognition

end

end OAI
