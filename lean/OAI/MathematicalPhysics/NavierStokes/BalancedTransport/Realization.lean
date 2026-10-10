import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Comparison
import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Periodic

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry

theorem prescribed_residual_realization {K : Set Space} (hK : IsCompact K)
    {U : Velocity} (hU : JointSmooth U) (hs : SpatiallySupported K U)
    (hp : RepeatsAfter 1 U) (hzero : ∀ x, U 0 x = 0)
    (hdiv : ∀ t, 0 ≤ t → ∀ x, div U t x = 0) :
    Smooth U ∧ Smooth (inertialCoefficient U) ∧ Smooth (viscousCoefficient U) ∧
    CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ BoundedMixed (inertialCoefficient U) ∧ BoundedMixed (viscousCoefficient U) ∧
    PeriodicAfterOne U ∧ ComparisonClass U (fun _ _ => 0) ∧
    (∃ X, IsMaterialFlow U X ∧ ∀ Y, IsMaterialFlow U Y →
      ∀ t, 0 ≤ t → ∀ x, X t x = Y t x) ∧
    ∀ ν : ℝ, 0 < ν → let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧ UniqueInComparison ν f U := by
  obtain ⟨hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hres⟩ :=
    prescribed_residual_regularity hK hU hs hp hzero hdiv
  have hclass := comparisonClass_of_compact_boundedMixed hK hU hs hbound
  obtain ⟨X, hX⟩ := exists_materialFlow_of_boundedMixed hU hbound
  obtain ⟨K', hK'⟩ := spatial_lipschitz_of_boundedMixed hU hbound
  refine ⟨hU.smooth, hf₀, hf₁, hsupport, hbound, hb₀, hb₁, hperiod, hclass,
    ⟨X, hX, fun Y hY t ht x => materialFlow_unique hK' hX hY ht x⟩, ?_⟩
  intro ν hν
  obtain ⟨hsol, hsm, hb, hp'⟩ := hres ν
  exact ⟨hsol, hsm, hb, hp', Analysis.unique_in_comparison hν.le hsol hclass⟩

theorem loaded_template_analytic_realization (z : Space) {η : ℝ} (hη : 0 < η)
    {K : Set Space} (hK : IsCompact K) {v : Velocity}
    (hv : JointSmooth v) (hc : TimeCollars v) (hs : SpatiallySupported K v)
    (hd : ∀ t x, div v t x = 0) :
    let U := loadedRepeat (loadingVelocity z η) v
    Smooth U ∧ CommonCompactSupport U (inertialCoefficient U) (viscousCoefficient U) ∧
    BoundedMixed U ∧ ComparisonClass U (fun _ _ => 0) ∧
    Function.Periodic (repeatTemplate v) 1 ∧
    (∀ t, 1 ≤ t → U t = repeatTemplate v t) ∧
    (∃ X, IsMaterialFlow U X) ∧
    ∀ ν : ℝ, 0 < ν → let f := affineForce (inertialCoefficient U) (viscousCoefficient U) ν
      ZeroDataSolution ν f U (fun _ _ => 0) ∧
      Smooth f ∧ BoundedMixed f ∧ PeriodicAfterOne f ∧ UniqueInComparison ν f U := by
  obtain ⟨hU, hUs, _, hzero, hrep, heq, hflow, _⟩ :=
    loaded_template_realization z hη hK hv hc hs hd
  have hlc : TimeCollars (loadingVelocity z η) := fun _ ht => loadingVelocity_zero ht
  have hdiv := fun t (_ : 0 ≤ t) x =>
    loadedRepeat_divergence (loadingVelocity_jointSmooth z η) hv hc
      (loadingVelocity_divergence z η) hd t x
  have hr := prescribed_residual_realization ((loadingSupport_compact z η).union hK)
    hU hUs (loadedRepeat_repeats (v := v) hlc) hzero hdiv
  exact ⟨hr.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1,
    hrep, heq, hflow, hr.2.2.2.2.2.2.2.2.2.2⟩

end BalancedTransport.Geometry
end

end OAI
