import OAI.Analysis.CoulombTransport.GraphBridge

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem356.IsometryTransport

/-- Apply the same spatial isometry to each particle. -/
def lift (e : E3 ≃ᵢ E3) : Triple ≃ᵐ Triple :=
  e.toHomeomorph.toMeasurableEquiv.prodCongr
    (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv)

@[simp] theorem lift_apply (e : E3 ≃ᵢ E3) (t : Triple) :
    lift e t = (e t.1, (e t.2.1, e t.2.2)) := rfl

@[simp] theorem invDistance_apply (e : E3 ≃ᵢ E3) (x y : E3) :
    invDistance (e x) (e y) = invDistance x y := by
  simp only [invDistance, ← dist_eq_norm, e.dist_eq]

@[simp] theorem cost_lift (e : E3 ≃ᵢ E3) (t : Triple) :
    coulombCost (lift e t) = coulombCost t := by
  simp only [coulombCost, lift_apply, tripleFst, tripleSnd, tripleThd,
    invDistance_apply]

theorem lintegral_map_lift (e : E3 ≃ᵢ E3) (pi : Measure Triple) :
    (∫⁻ t, coulombCost t ∂Measure.map (lift e) pi) = ∫⁻ t, coulombCost t ∂pi := by
  rw [lintegral_map_equiv]
  simp only [cost_lift]

theorem coupling_map_lift (e : E3 ≃ᵢ E3) {mu : Measure E3} {pi : Measure Triple}
    (hpi : IsThreeCoupling mu pi) :
    IsThreeCoupling (Measure.map e mu) (Measure.map (lift e) pi) := by
  have := hpi.1
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.map_map measurable_tripleFst (lift e).measurable,
      ← hpi.2.1, Measure.map_map e.continuous.measurable measurable_tripleFst]
    rfl
  · rw [Measure.map_map measurable_tripleSnd (lift e).measurable,
      ← hpi.2.2.1, Measure.map_map e.continuous.measurable measurable_tripleSnd]
    rfl
  · rw [Measure.map_map measurable_tripleThd (lift e).measurable,
      ← hpi.2.2.2, Measure.map_map e.continuous.measurable measurable_tripleThd]
    rfl

theorem kantorovichValue_map_le (e : E3 ≃ᵢ E3) (mu : Measure E3) :
    kantorovichValue (Measure.map e mu) ≤ kantorovichValue mu := by
  unfold kantorovichValue
  refine le_iInf fun pi => le_iInf fun hpi => ?_
  calc
    _ ≤ ∫⁻ t, coulombCost t ∂Measure.map (lift e) pi :=
      iInf₂_le _ (coupling_map_lift e hpi)
    _ = _ := lintegral_map_lift e pi

theorem kantorovichValue_map (e : E3 ≃ᵢ E3) (mu : Measure E3) :
    kantorovichValue (Measure.map e mu) = kantorovichValue mu := by
  apply le_antisymm (kantorovichValue_map_le e mu)
  have h := kantorovichValue_map_le e.symm (Measure.map e mu)
  simpa only [Measure.map_map e.symm.continuous.measurable e.continuous.measurable,
    IsometryEquiv.symm_comp_self, Measure.map_id] using h

/-- Transport a bounded-domain supporting potential without changing the cost. -/
theorem supporting_inequality_image (e : E3 ≃ᵢ E3) (U : Set E3) (u : E3 → ℝ)
    (h : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U,
      ENNReal.ofReal (u x + u y + u z) ≤ coulombCost (x, (y, z))) :
    ∀ x ∈ e '' U, ∀ y ∈ e '' U, ∀ z ∈ e '' U,
      ENNReal.ofReal (u (e.symm x) + u (e.symm y) + u (e.symm z)) ≤
        coulombCost (x, (y, z)) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  change ENNReal.ofReal (u (e.symm (e x)) + u (e.symm (e y)) +
    u (e.symm (e z))) ≤ coulombCost (lift e (x, (y, z)))
  rw [cost_lift]
  simpa only [e.symm_apply_apply] using h x hx y hy z hz

theorem supporting_equality_image (e : E3 ≃ᵢ E3) (u : E3 → ℝ) (t : Triple) :
    coulombCost (lift e t) = ENNReal.ofReal
      (u (e.symm (tripleFst (lift e t))) +
        u (e.symm (tripleSnd (lift e t))) + u (e.symm (tripleThd (lift e t)))) ↔
    coulombCost t = ENNReal.ofReal (u (tripleFst t) + u (tripleSnd t) + u (tripleThd t)) := by
  rw [cost_lift]
  simp only [lift_apply, tripleFst, tripleSnd, tripleThd, e.symm_apply_apply]

/-- Orthogonal changes of variables transport a density without a Jacobian factor. -/
theorem map_densityMeasure (e : E3 ≃ₗᵢ[ℝ] E3) (rho : E3 → ℝ)
    (hrho : Measurable rho) :
    Measure.map e (densityMeasure rho) = densityMeasure (fun x => rho (e.symm x)) := by
  ext s hs
  rw [Measure.map_apply e.continuous.measurable hs, densityMeasure,
    withDensity_apply _ (e.continuous.measurable hs), densityMeasure,
    withDensity_apply _ hs]
  conv_rhs => rw [← e.measurePreserving.map_eq]
  have hm : Measurable (fun a : E3 => ENNReal.ofReal (rho (e.symm a))) :=
    (hrho.comp e.symm.continuous.measurable).ennreal_ofReal
  rw [setLIntegral_map (μ := (volume : Measure E3)) hs hm e.continuous.measurable]
  simp only [e.symm_apply_apply]

theorem smoothDensity_comp_symm (e : E3 ≃ₗᵢ[ℝ] E3) {rho : E3 → ℝ}
    (hrho : IsSmoothCompactProbabilityDensity rho) :
    IsSmoothCompactProbabilityDensity (fun x => rho (e.symm x)) := by
  refine ⟨fun x => hrho.1 _, hrho.2.1.comp e.symm.contDiff,
    hrho.2.2.1.comp_homeomorph e.symm.toHomeomorph,
    hrho.2.2.2.1.comp e.symm.contDiff,
    hrho.2.2.2.2.1.comp_homeomorph e.symm.toHomeomorph, ?_⟩
  rw [e.symm.measurePreserving.integral_comp e.symm.toMeasurableEquiv.measurableEmbedding]
  exact hrho.2.2.2.2.2

/-- Exchange the first and second Euclidean axes, leaving the third fixed. -/
def axisSwap : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)

@[simp] theorem axisSwap_single (i : Fin 3) (a : ℝ) :
    axisSwap (PiLp.single 2 i a) = PiLp.single 2 (Equiv.swap 0 1 i) a := by
  exact LinearIsometryEquiv.piLpCongrLeft_single _ _ _

@[simp] theorem axisSwap_zero : axisSwap (0 : E3) = 0 := map_zero axisSwap

@[simp] theorem axisSwap_first :
    axisSwap (PiLp.single 2 (0 : Fin 3) (1 : ℝ)) = PiLp.single 2 (1 : Fin 3) (1 : ℝ) := by
  simp

@[simp] theorem axisSwap_second :
    axisSwap (PiLp.single 2 (1 : Fin 3) (1 : ℝ)) = PiLp.single 2 (0 : Fin 3) (1 : ℝ) := by
  simp

end Problem356.IsometryTransport

end

end OAI
