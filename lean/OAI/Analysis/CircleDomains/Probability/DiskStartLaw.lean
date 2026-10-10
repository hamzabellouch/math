import OAI.Analysis.CircleDomains.Probability.CenteredArcLaw

namespace OAI

/-! Atomlessness and the boundary measure for the actual disk arc law. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem normalizedArgument_injOn_unit_sphere :
    InjOn normalizedArgument {z : ℂ | ‖z‖ = 1} := by
  intro z hz w hw h
  apply Complex.ext_norm_arg (hz.trans hw.symm)
  apply Complex.arg_coe_angle_eq_iff.mp
  exact (AddCircle.equivAddCircle (2 * Real.pi) 1 (by positivity) one_ne_zero).injective h

theorem diskStartingAngleLaw_atomless (η : ProbabilityMeasure C(PathTime, ℂ))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), ‖γ 0‖ = 1)
    (havoid : ∀ z : ℂ, ‖z‖ = 1 → pathHitProbability η z = 0) :
    NullSingletonClass (arcStartingAngleLaw η : Measure UnitAddCircle) := by
  constructor
  intro θ
  rw [arcStartingAngleLaw, ProbabilityMeasure.map_apply' η
    measurable_arcStartingAngle.aemeasurable (measurableSet_singleton θ)]
  by_cases hz : ∃ z : ℂ, ‖z‖ = 1 ∧ normalizedArgument z = θ
  · obtain ⟨z, hz, hθ⟩ := hz
    apply le_antisymm ?_ bot_le
    calc
      (η : Measure C(PathTime, ℂ))
          ((fun γ => normalizedArgument (γ 0)) ⁻¹' {θ}) ≤ pathHitProbability η z := by
        apply measure_mono_ae
        filter_upwards [hη] with γ hγ he
        exact ⟨0, normalizedArgument_injOn_unit_sphere hγ hz (he.trans hθ.symm)⟩
      _ = 0 := havoid z hz
  · apply measure_mono_null (t := {γ : C(PathTime, ℂ) | ¬ ‖γ 0‖ = 1})
    · intro γ he hγ
      exact hz ⟨γ 0, hγ, he⟩
    · exact ae_iff.mp hη

theorem diskTerminalArc_norm_le {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet)
    (t : PathTime) : ‖γ t‖ ≤ 1 := by
  by_cases h0 : t = 0
  · simpa only [h0, hγ.2.1] using (le_refl (1 : ℝ))
  by_cases h1 : t = 1
  · simp only [h1, hγ.2.2.1, norm_zero, zero_le_one]
  exact (hγ.2.2.2 t ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm h0),
    lt_of_le_of_ne (unitInterval.le_one t) h1⟩).le

theorem diskArcLaw_boundary_data (η : ProbabilityMeasure C(PathTime, ℂ))
    (hη : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)), γ ∈ diskTerminalArcSet)
    (havoid : ∀ z : ℂ, ‖z‖ = 1 → pathHitProbability η z = 0) :
    NullSingletonClass (arcStartingAngleLaw η : Measure UnitAddCircle) ∧
    ∀ p : CircleLiftCover normalizedArgument, ‖p.base‖ = 1 →
      Integrable (fun γ => totalDiskArcIndex γ p) (η : Measure C(PathTime, ℂ)) ∧
      meanDiskArcIndex η p = boundaryIndexMean (arcStartingAngleLaw η) p.height := by
  refine ⟨diskStartingAngleLaw_atomless η (hη.mono fun _ h => h.2.1) havoid, ?_⟩
  intro p hp
  have hg : ∀ᵐ γ ∂(η : Measure C(PathTime, ℂ)),
      ‖γ 0‖ = 1 ∧ γ 1 = 0 ∧ ∀ t, ‖γ t‖ ≤ 1 :=
    hη.mono fun _ h => ⟨h.2.1, h.2.2.1, diskTerminalArc_norm_le h⟩
  exact ⟨integrable_totalDiskArcIndex_boundary η p hp hg (havoid _ hp),
    meanDiskArcIndex_boundary η p hp hg (havoid _ hp)⟩

end CircleDomainRigidity

end

end OAI
