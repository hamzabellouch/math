import OAI.Analysis.KadisonKastler.WeightedStripOperator
import OAI.Analysis.KadisonKastler.ModularCyclicGroup

namespace OAI

/-! # Identifying the weighted strip through cyclic spectral coordinates -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem weightedStripOperator_eq_group (a t : ℝ) (ha : |a| < 1)
    (g : C(spectrum ℝ (graphResolvent M J Ω 1), ℂ))
    (hg : ∀ s : spectrum ℝ (graphResolvent M J Ω 1), 0 < s.val → s.val < 1 →
      weightedStripKernel ((a : ℂ) + t * Complex.I) s.val = g s * modularSpectralPhase t s.val) :
    weightedStripOperator (M := M) J Ω ((a : ℂ) + t * Complex.I) =
      resolventContinuousCalculus (graphResolvent M J Ω 1)
        (graphResolvent_positive J Ω 1).isSelfAdjoint g *
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ (x : H) := resolventVectorMeasure R hR x
  let F := weightedStripContinuous (resolventRealCoordinate R) ((a : ℂ) + t * Complex.I)
  have hz : |(((a : ℂ) + t * Complex.I)).re| < 1 := by simpa using ha
  apply ContinuousLinearMap.ext
  intro x
  let e : ResolventCyclicL2 R hR x := ContinuousMap.toLp 2 (μ x) ℂ 1
  let w := modularCyclicPhaseOperator M J Ω x t e
  have hwe : w =ᵐ[μ x] fun s => modularSpectralPhase t s.val * e s :=
    resolventScalarMultiplier_apply_ae R hR x _ _ _ _ e
  have heq : ContinuousMap.toLp 2 (μ x) ℂ F =
      resolventScalarMultiplier R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w := by
    apply Lp.ext
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ x) F,
      resolventScalarMultiplier_apply_ae R hR x g g.continuous.measurable ‖g‖ g.norm_coe_le_norm w,
      hwe, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) (μ x) (1 : C(spectrum ℝ R, ℂ)),
      graphResolventVectorMeasure_interior J Ω hsep hcyc x] with s hF hgm hw he hs
    rw [hF, hgm, hw, he, ContinuousMap.one_apply, mul_one]
    exact (weightedStripContinuous_apply _ hz s).trans (hg s hs.1 hs.2)
  calc
    weightedStripOperator (M := M) J Ω ((a : ℂ) + t * Complex.I) x =
        resolventCyclicIsometry R hR x (ContinuousMap.toLp 2 (μ x) ℂ F) :=
      (resolventCyclicIsometry_continuous R hR x F).symm
    _ = resolventContinuousCalculus R hR g (resolventCyclicIsometry R hR x w) := by
      rw [heq, resolventCyclicIsometry_multiplier]
    _ = _ := by
      rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc x t e,
        resolventCyclicIsometry_one]
      rfl

end

end KadisonKastler

end OAI
