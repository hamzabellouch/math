import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarCompactBridge
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarTransition

namespace OAI

/-! Bounds and actual global transitions for the compact planar version of
the normalized program. The periodic spatial expression agrees on the
chart; outside the common support all derivatives vanish. -/

noncomputable section
namespace ForcedComputation.Recorder.Planar
open ShearFlows PlanarHamiltonian Set Filter
open scoped Topology ContDiff NNReal

def compactVelocity (I : Alternating.MachineInput) (hI : Alternating.ValidInput I)
    (s : ℝ) : Plane → Plane :=
  PlanarHamiltonian.periodicVelocity
    (n := (actions (freshMachine I.1) (freshInput_wellFormed hI)).length)
    (normalizedPulse I hI) s

theorem compactVelocity_smooth (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ContDiff ℝ ∞ (fun y : ℝ × Plane => compactVelocity I hI y.1 y.2) :=
  periodicVelocity_smooth (normalizedPulse_valid I hI)

theorem compactVelocity_germ (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) {x : Plane}
    (hx₀ : x 0 ∈ Ioo (0 : ℝ) 1) (hx₁ : x 1 ∈ Ioo (0 : ℝ) 1) :
    compactVelocity I hI s =ᶠ[𝓝 x] planarSlice (normalizedHamiltonian I hI) s := by
  have ho : IsOpen {y : Plane | y 0 ∈ Ioo (0 : ℝ) 1 ∧ y 1 ∈ Ioo (0 : ℝ) 1} :=
    (isOpen_Ioo.preimage (continuous_apply 0)).inter
      (isOpen_Ioo.preimage (continuous_apply 1))
  filter_upwards [ho.mem_nhds ⟨hx₀, hx₁⟩] with y hy
  exact normalized_planar_field_on_chart I hI s y hy.1 hy.2

theorem compactVelocity_support (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) :
    tsupport (compactVelocity I hI s) ⊆ commonSupport (normalizedPulse I hI) :=
  (periodicVelocity_properties (normalizedPulse_valid I hI) s).1

theorem compactVelocity_off_chart (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) {x : Plane}
    (hx : ¬ (x 0 ∈ Ioo (0 : ℝ) 1 ∧ x 1 ∈ Ioo (0 : ℝ) 1)) :
    x ∉ tsupport (compactVelocity I hI s) := by
  intro hm
  have h := commonSupport_in_unit (normalizedPulse_inUnit I hI)
    (compactVelocity_support I hI s hm)
  exact hx ⟨h 0, h 1⟩

theorem compactVelocity_bound (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) (x : Plane) :
    ‖compactVelocity I hI s x‖ ≤
      ((SpatialExpression.suspensionCode (normalizedHamiltonian I hI)).bound [] : ℝ) := by
  by_cases hx : x 0 ∈ Ioo (0 : ℝ) 1 ∧ x 1 ∈ Ioo (0 : ℝ) 1
  · rw [(compactVelocity_germ I hI s hx.1 hx.2).eq_of_nhds]
    exact planarSlice_bound (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) s x
  · rw [image_eq_zero_of_notMem_tsupport (compactVelocity_off_chart I hI s hx), norm_zero]
    exact Nat.cast_nonneg _

theorem compactVelocity_derivative_bounds (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) (x : Plane) :
    ‖fderiv ℝ (compactVelocity I hI s) x‖ ≤
        (planarVariationCoefficient (normalizedHamiltonian I hI) : ℝ) ∧
      ‖fderiv ℝ (fderiv ℝ (compactVelocity I hI s)) x‖ ≤
        (planarVariationCoefficient (normalizedHamiltonian I hI) : ℝ) := by
  by_cases hx : x 0 ∈ Ioo (0 : ℝ) 1 ∧ x 1 ∈ Ioo (0 : ℝ) 1
  · have he := compactVelocity_germ I hI s hx.1 hx.2
    rw [he.fderiv_eq, he.fderiv.fderiv_eq]
    exact planar_derivative_bounds (normalizedHamiltonian_valid I hI)
      (normalizedHamiltonian_noTime I hI) s x
  · have hn := compactVelocity_off_chart I hI s hx
    have hn' : x ∉ tsupport (fderiv ℝ (compactVelocity I hI s)) :=
      fun h => hn (tsupport_fderiv_subset ℝ h)
    constructor
    · rw [fderiv_of_notMem_tsupport ℝ hn, norm_zero]
      exact Nat.cast_nonneg _
    · have hz := fderiv_of_notMem_tsupport ℝ hn'
      exact (congrArg norm hz).le.trans ((ContinuousLinearMap.opNorm_zero :
        ‖(0 : Plane →L[ℝ] (Plane →L[ℝ] Plane))‖ = 0).le.trans (Nat.cast_nonneg _))

theorem compactVelocity_lipschitz (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) (s : ℝ) :
    LipschitzWith (planarVariationCoefficient (normalizedHamiltonian I hI) : ℝ≥0)
      (compactVelocity I hI s) := by
  have hi : ContDiff ℝ ∞ (fun x : Plane => (s, x)) :=
    contDiff_const.prodMk contDiff_id
  have hs := (compactVelocity_smooth I hI).comp hi
  apply lipschitzWith_of_nnnorm_fderiv_le (hs.differentiable (by simp))
  intro x
  exact_mod_cast (compactVelocity_derivative_bounds I hI s x).1

theorem compactVelocity_transitions (I : Alternating.MachineInput)
    (hI : Alternating.ValidInput I) :
    ∃ Ψ, IsPlanarTransition (compactVelocity I hI) Ψ := by
  apply exists_planarTransition_of_bounds (B :=
    ((SpatialExpression.suspensionCode (normalizedHamiltonian I hI)).bound [] : ℝ≥0))
    (compactVelocity_lipschitz I hI)
  · intro x
    have hi : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    have h := (compactVelocity_smooth I hI).continuous.comp hi
    exact h
  · exact compactVelocity_bound I hI

end ForcedComputation.Recorder.Planar

end

end OAI
