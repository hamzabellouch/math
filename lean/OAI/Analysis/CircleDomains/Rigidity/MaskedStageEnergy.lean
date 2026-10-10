import OAI.Analysis.CircleDomains.Rigidity.MaskedCoordinateStage
import OAI.Analysis.CircleDomains.Sobolev.EnergyTransportIntegrability
import OAI.Analysis.CircleDomains.Sobolev.ComplexCovectorEnergy

namespace OAI

/-! Integrability and full masked energy on the actual finite model.
The geometric facts retained from construction justify comparison of
ordinary integrals on all later subregions. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {C : Fin n → MaskedCoordinateData G U π σ} {Flag : Set S} {O : S → Set Sphere}
  {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}

 theorem MaskedCoordinateStage.integrable_energy
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π) (l : Fin n) :
    IntegrableOn (fieldEnergy (circleGradient (T.model.functions l)) T.model.metric)
      (realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask) := by
  have hM : IsClosed (physicalMask π (C l).mask) :=
    (C l).mask_closed.preimage (hπ.comp (OnePoint.continuous_coe.comp Complex.equivRealProdCLM.symm.continuous))
  have hi : MemLp (circleGradient (C l).physical) 2
      (volume.restrict (realChartDomain G ∩ physicalMask π (C l).mask)) := by
    simpa only [Measure.restrict_restrict hM.measurableSet, inter_comm] using (C l).energy
  exact integrableOn_masked_circle_energy
    ((isOpen_realChartDomain hG).union (isOpen_iUnion fun j => (realJordanInterior_geometry (T.filling j)).1))
    (isClosed_real_completedRegion T.terminals.H) T.core_closed T.core_cocompact
    (fun _ hx => T.model.extension_contains hx.1) T.core_source hM (T.model.mask_boundary_core l)
    (T.model.filled.1 l) hi (T.model.retained.mono fun _ hx => hx l)
    T.model.metric_smooth.continuous T.model.metric_pos T.model.metric_core

 theorem MaskedCoordinateStage.energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) :
    (∫ x in realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask,
      fieldEnergy (circleGradient (T.model.functions l)) T.model.metric x) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  simpa only [sdiff_empty] using T.model.localized l ∅ MeasurableSet.empty (empty_subset _)

def MaskedCoordinateStage.sourceMask
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) : Set (ℝ × ℝ) :=
  realChartDomain (openCompletedRegion T.terminals.H) ∩ interior (physicalMask π (C l).mask)

def MaskedCoordinateStage.targetMask
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (l : Fin n) : Set (ℝ × ℝ) :=
  sphereRealMap T.model.forward '' T.sourceMask l

 theorem MaskedCoordinateStage.transported_energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n) :
    IntegrableOn (fieldEnergy (circleGradient (T.model.functions l ∘ sphereRealMap T.model.inverse))
      (fun _ => 1)) (T.targetMask l) ∧
    (∫ y in T.targetMask l,
      fieldEnergy (circleGradient (T.model.functions l ∘ sphereRealMap T.model.inverse)) (fun _ => 1) y) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  let : Fintype T.indices := T.indices_finite.fintype
  have hsource : IsOpen (T.sourceMask l) :=
    (isOpen_realChartDomain (isOpen_openCompletedRegion T.terminals.H)).inter isOpen_interior
  have hsub : T.sourceMask l ⊆
      realChartDomain (completedRegion T.terminals.H) ∩ physicalMask π (C l).mask :=
    fun _ hx => ⟨openCompletedRegion_subset_completedRegion T.terminals.H hx.1, interior_subset hx.2⟩
  have hi := T.integrable_energy hG hπ l
  have his := hi.mono_set hsub
  have htarget := T.model.transported l
  have hUinf : OnePoint.infty ∈ openCompletedRegion T.terminals.H :=
    T.core_model (infty_mem_sphericalCore T.core)
  have hmeas := hsource.measurableSet
  have hit := (integrable_filled_circleEnergy_metric_sphere_map_iff hmeas htarget.1
    T.model.equivalence.bijOn.injOn (fun _ hx => hx.1) hmetric
    (fun x _ => T.model.metric_pos x)
    (fun x hx => finite_image_of_fixes_infty T.model.equivalence.bijOn.injOn hUinf
      T.model.principal.1 hx.1)
    (fun x hx => mem_image_of_mem _ hx)
    (T.model.functions l ∘ sphereRealMap T.model.inverse) (T.model.functions l)
    htarget.2.1 htarget.2.2).mpr his
  refine ⟨hit, ?_⟩
  rw [MaskedCoordinateStage.targetMask, T.model.transported_energy l (T.sourceMask l) hmeas (Subset.refl _)]
  exact (setIntegral_mono_set hi
    (ae_of_all _ (fun x => covectorEnergy_nonneg _ (T.model.metric_pos x)))
    (ae_of_all _ hsub)).trans_lt (T.energy_lt l)

 theorem MaskedCoordinateStage.complex_energy_lt
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hG : IsOpen G) (hπ : Continuous π)
    (hmetric : ∀ p ∈ openCompletedRegion T.terminals.H,
      IsMetricConformalAt T.model.metric T.model.forward p) (l : Fin n) :
    MemLp (circleFDeriv ((T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM))
      2 (volume.restrict (Complex.equivRealProdCLM ⁻¹' T.targetMask l)) ∧
    (∫ z in Complex.equivRealProdCLM ⁻¹' T.targetMask l,
      ‖circleFDeriv ((T.model.functions l ∘ sphereRealMap T.model.inverse) ∘ Complex.equivRealProdCLM) z‖ ^ 2) <
      (∫ x in realChartDomain G ∩ physicalMask π (C l).mask,
        fieldEnergy (circleGradient (C l).physical) (fun x => sphericalMetricFactor x • 1) x) + ε := by
  have htarget := T.model.transported l
  obtain ⟨hi, he⟩ := T.transported_energy_lt hG hπ hmetric l
  refine ⟨memLp_circleFDeriv_complex htarget.1 htarget.1.measurableSet (Subset.refl _) htarget.2.1 hi, ?_⟩
  rw [integral_circleFDeriv_complex_norm_sq (D := T.targetMask l) (A := T.targetMask l) htarget.1 htarget.1.measurableSet (Subset.refl _) htarget.2.1]
  exact he

end CircleDomainRigidity.FiniteTransfer

end

end OAI
