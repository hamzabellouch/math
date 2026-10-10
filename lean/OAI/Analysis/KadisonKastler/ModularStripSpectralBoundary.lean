import OAI.Analysis.KadisonKastler.ModularSpectralStrip
import OAI.Analysis.KadisonKastler.ModularStripBoundary
import OAI.Analysis.KadisonKastler.ModularCyclicGroup
import OAI.Analysis.KadisonKastler.ResolventCoordinateMultiplier

namespace OAI

/-! # Operator boundary values of the spectral strip integral -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)

/-- A scalar spectral integral is the corresponding ambient matrix coefficient. -/
theorem modularSpectralStrip_eq_inner (X Y Z : H) (z : ℂ)
    (v : ResolventCyclicL2 (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y)
    (hv : v =ᵐ[resolventVectorMeasure (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y]
      fun s => modularStripKernel z s.val)
    (hZ : resolventCyclicIsometry (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y v = Z) :
    modularSpectralStrip (M := M) J Ω X Y z = inner ℂ X Z := by
  rw [← hZ]
  change _ = inner ℂ X ((resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint Y).toContinuousLinearMap v)
  rw [← ContinuousLinearMap.adjoint_inner_left, L2.inner_def]
  unfold modularSpectralStrip modularStripIntegral modularSpectralCoefficient
  apply integral_congr_ae
  filter_upwards [hv] with s hs
  rw [hs, RCLike.inner_apply]
  exact mul_comm _ _

variable [TopologicalSpace.SeparableSpace H]
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

private theorem cyclic_phase_one (Y : H) (t : ℝ) :
    resolventCyclicIsometry (graphResolvent M J Ω 1)
      (graphResolvent_positive J Ω 1).isSelfAdjoint Y
      (modularCyclicPhaseOperator M J Ω Y t
        (ContinuousMap.toLp 2 (resolventVectorMeasure (graphResolvent M J Ω 1)
          (graphResolvent_positive J Ω 1).isSelfAdjoint Y) ℂ 1)) =
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) Y := by
  rw [modularCyclicPhaseOperator_intertwines J Ω hsep hcyc Y,
    resolventCyclicIsometry_one]
  rfl

theorem modularSpectralStrip_bottom (X Y : H) (t : ℝ) :
    modularSpectralStrip (M := M) J Ω X Y (t : ℂ) =
      inner ℂ X (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) Y)) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR Y
  let e : ResolventCyclicL2 R hR Y := ContinuousMap.toLp 2 μ ℂ 1
  let w := modularCyclicPhaseOperator M J Ω Y (-t) e
  let v := resolventCoordinateOperator R hR Y w
  apply modularSpectralStrip_eq_inner J Ω X Y _ (t : ℂ) v
  · have hw : w =ᵐ[μ] fun s => modularSpectralPhase (-t) s.val * e s :=
      resolventScalarMultiplier_apply_ae R hR Y _ _ _ _ e
    filter_upwards [resolventCoordinateOperator_apply_ae R hR Y w, hw,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (1 : C(spectrum ℝ R, ℂ))]
      with s hv hw he
    rw [hv, hw, he, ContinuousMap.one_apply, mul_one, modularStripKernel_bottom]
  · exact (resolventCoordinateOperator_intertwines R hR Y w).trans
      (congrArg R (cyclic_phase_one J Ω hsep hcyc Y (-t)))

theorem modularSpectralStrip_top (X Y : H) (t : ℝ) :
    modularSpectralStrip (M := M) J Ω X Y ((t : ℂ) + Complex.I) =
      inner ℂ X ((1 - graphResolvent M J Ω 1)
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) Y)) := by
  let R := graphResolvent M J Ω 1
  have hR : IsSelfAdjoint R := (graphResolvent_positive J Ω 1).isSelfAdjoint
  let μ := resolventVectorMeasure R hR Y
  let e : ResolventCyclicL2 R hR Y := ContinuousMap.toLp 2 μ ℂ 1
  let w := modularCyclicPhaseOperator M J Ω Y (-t) e
  let v := (1 - resolventCoordinateOperator R hR Y) w
  apply modularSpectralStrip_eq_inner J Ω X Y _ ((t : ℂ) + Complex.I) v
  · have hw : w =ᵐ[μ] fun s => modularSpectralPhase (-t) s.val * e s :=
      resolventScalarMultiplier_apply_ae R hR Y _ _ _ _ e
    have hv : v =ᵐ[μ] fun s => w s - (resolventCoordinateOperator R hR Y w) s :=
      (Lp.coeFn_sub w (resolventCoordinateOperator R hR Y w))
    filter_upwards [hv, resolventCoordinateOperator_apply_ae R hR Y w, hw,
      ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) μ (1 : C(spectrum ℝ R, ℂ)),
      graphResolventVectorMeasure_interior J Ω hsep hcyc Y] with s hv hc hw he hs
    rw [hv, hc, hw, he, ContinuousMap.one_apply, mul_one,
      modularStripKernel_top hs.1 hs.2]
    push_cast
    ring
  · exact (one_sub_resolventCoordinateOperator_intertwines R hR Y w).trans
      (congrArg (fun v : H => (1 - R) v) (cyclic_phase_one J Ω hsep hcyc Y (-t)))

end

end KadisonKastler

end OAI
