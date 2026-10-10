import OAI.Analysis.CircleDomains.Topology.MeanIndexBoundary

namespace OAI

/-! On the unit boundary a terminal arc meets only its starting point.
Thus atomlessness of the starting law is exactly the needed point avoidance. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem diskTerminalArc_boundary_hit_iff
    {γ : C(PathTime, ℂ)} (hγ : γ ∈ diskTerminalArcSet) {w : ℂ} (hw : ‖w‖ = 1) :
    w ∈ range γ ↔ γ 0 = w := by
  constructor
  · rintro ⟨t, ht⟩
    by_cases h0 : t = 0
    · simpa only [h0] using ht
    by_cases h1 : t = 1
    · rw [h1, hγ.2.2.1] at ht
      have hh := hw
      rw [← ht, norm_zero] at hh
      norm_num at hh
    · have hlt := hγ.2.2.2 t ⟨lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm h0),
        lt_of_le_of_ne (unitInterval.le_one t) h1⟩
      rw [ht, hw] at hlt
      exact (lt_irrefl _ hlt).elim
  · intro h
    exact ⟨0, h⟩

 theorem compactArc_boundary_avoidance
    (K : Set C(PathTime, ℂ)) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)] (x : ℝ) :
    ∀ᵐ γ : K ∂(η : Measure K), diskRayProjection (x : ℂ) ∉ range γ.val := by
  have hnull : (η : Measure K) ((fun γ : K => normalizedArgument (γ.val 0)) ⁻¹'
      {(x : UnitAddCircle)}) = 0 := by
    rw [← ProbabilityMeasure.map_apply' η (measurable_compactArcStartingAngle K).aemeasurable
      (measurableSet_singleton (x : UnitAddCircle))]
    change (compactArcStartingAngleLaw K η : Measure UnitAddCircle) {(x : UnitAddCircle)} = 0
    exact measure_singleton _
  have ha : ∀ᵐ γ : K ∂(η : Measure K), normalizedArgument (γ.val 0) ≠ (x : UnitAddCircle) :=
    by
      apply ae_iff.mpr
      have hs : {γ : K | ¬ normalizedArgument (γ.val 0) ≠ (x : UnitAddCircle)} =
          ((fun γ : K => normalizedArgument (γ.val 0)) ⁻¹' {(x : UnitAddCircle)}) := by
        ext γ
        simp only [mem_ofPred_eq, not_not, mem_preimage, mem_singleton_iff]
      rw [hs]
      exact hnull
  filter_upwards [ha] with γ hγ hh
  have hw : ‖diskRayProjection (x : ℂ)‖ = 1 := by
    simp only [diskRayProjection_norm, Complex.ofReal_im, neg_zero, Real.exp_zero]
  have he := (diskTerminalArc_boundary_hit_iff (hKS γ.property) hw).mp hh
  apply hγ
  rw [he, diskRayProjection_argument, Complex.ofReal_re]

end CircleDomainRigidity

end

end OAI
