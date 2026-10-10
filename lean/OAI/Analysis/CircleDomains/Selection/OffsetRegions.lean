import OAI.Analysis.CircleDomains.Sobolev.FinitePeriodStokes

namespace OAI

/-! Geometry and energy monotonicity for the actual regions obtained by
moving finitely many round boundaries a common positive distance. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem offset_closed_region_subset
    {I : Type*} (H : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    closure (jordanInterior H) \ ⋃ i, ball (c i) (r i + ρ) ⊆
      closure (jordanInterior H) \ ⋃ i, closedBall (c i) (r i) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rintro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  apply hz.2
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [mem_ball]
  exact (mem_closedBall.mp hi).trans_lt (by linarith)

 theorem offset_open_region_subset
    {I : Type*} (H : ℂ ≃ₜ ℂ) (c : I → ℂ) (r : I → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    jordanInterior H \ ⋃ i, closedBall (c i) (r i + ρ) ⊆
      jordanInterior H \ ⋃ i, closedBall (c i) (r i) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rintro hm
  obtain ⟨i, hi⟩ := mem_iUnion.mp hm
  exact hz.2 (mem_iUnion.mpr ⟨i, closedBall_subset_closedBall (by linarith) hi⟩)

 theorem circle_energy_mono {S T : Set ℂ} (hST : S ⊆ T)
    (u : ℂ → UnitAddCircle) (hE : MemLp (circleFDeriv u) 2 (volume.restrict T)) :
    Real.sqrt (∫ z in S, ‖circleFDeriv u z‖ ^ 2) ≤
      Real.sqrt (∫ z in T, ‖circleFDeriv u z‖ ^ 2) := by
  apply Real.sqrt_le_sqrt
  exact setIntegral_mono_set (hE.integrable_norm_pow (p := 2) (by norm_num))
    (Eventually.of_forall fun _ => sq_nonneg _)
    (Eventually.of_forall fun _ hz => hST hz)

end CircleDomainRigidity

end

end OAI
