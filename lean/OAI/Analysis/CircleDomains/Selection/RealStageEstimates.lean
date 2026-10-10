import OAI.Analysis.CircleDomains.Transfer.RealTransferStage
import OAI.Analysis.CircleDomains.Sobolev.TransportedRealEnergy

namespace OAI

/-! Analytic and geometric consequences of an actual real transfer stage. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n : ℕ} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {u : Fin n → (ℝ × ℝ) → ℝ} {a b : Fin n → S → ℝ}
  {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε : ℝ}

namespace RealTransferStage

variable (M : RealTransferStage G π σ u a b Flag O K₀ ε)

theorem source_infty : OnePoint.infty ∈ openCompletedRegion M.terminals.H :=
  M.core_model (infty_mem_sphericalCore M.core)

theorem prescribed_core_model : sphericalCore K₀ ⊆ openCompletedRegion M.terminals.H :=
  (sphericalCore_mono (M.core_contains.trans interior_subset)).trans M.core_model

theorem prescribed_core_conformal : IsConformalOn M.forward (sphericalCore K₀) :=
  M.conformal_core.mono (sphericalCore_mono (M.core_contains.trans interior_subset))

theorem functions_smooth_source (l : Fin n) :
    ContDiffOn ℝ ∞ (M.functions l) (realChartDomain (openCompletedRegion M.terminals.H)) :=
  (M.functions_smooth l).mono
    ((preimage_mono (openCompletedRegion_subset_completedRegion M.terminals.H)).trans
      M.extension_contains)

theorem functions_integrable_source (l : Fin n) :
    IntegrableOn (gradientEnergy (M.functions l) M.metric)
      (realChartDomain (openCompletedRegion M.terminals.H)) :=
  (M.integrable l).mono_set
    (preimage_mono (openCompletedRegion_subset_completedRegion M.terminals.H))

theorem source_energy_lt (l : Fin n) :
    (∫ x in realChartDomain (openCompletedRegion M.terminals.H),
      gradientEnergy (M.functions l) M.metric x) <
    (∫ x in realChartDomain G,
      gradientEnergy (u l) (fun z => sphericalMetricFactor z • 1) x) + ε := by
  have h := M.source_energy l ∅ MeasurableSet.empty (empty_subset _)
  simp only [sdiff_empty] at h
  apply lt_of_le_of_lt _ h
  exact setIntegral_mono_set (M.integrable l)
    (ae_of_all _ (fun x => gradientEnergy_nonneg _ M.metric_pos x))
    (Eventually.of_forall fun x hx => openCompletedRegion_subset_completedRegion M.terminals.H hx)

theorem retained_on_core (l : Fin n) : EqOn (M.functions l) (u l) M.core := by
  intro x hx
  exact (M.retained.self_of_nhdsSet x hx) l

theorem terminal_frontier_extension (i : M.indices) :
    frontier (realJordanInterior (M.terminals.H i)) ⊆ M.extension := by
  rw [frontier_realJordanInterior]
  rintro x ⟨z, hz, rfl⟩
  apply M.extension_contains
  change (z : Sphere) ∈ completedRegion M.terminals.H
  intro hbad
  obtain ⟨j, w, hw, heq⟩ := mem_iUnion.mp hbad
  have hwz : w = z := OnePoint.coe_injective heq
  subst w
  by_cases hij : i = j
  · subst j
    exact Set.disjoint_left.mp
      (disjoint_frontier_iff_isOpen.mpr (jordanInterior_isOpen (M.terminals.H i))) hz hw
  · exact Set.disjoint_left.mp (M.terminals.disjoint_closures hij)
      (frontier_subset_closure hz) (subset_closure hw)

end RealTransferStage

end CircleDomainRigidity.FiniteTransfer

end

end OAI
