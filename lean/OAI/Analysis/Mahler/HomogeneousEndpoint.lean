import OAI.Analysis.Mahler.HomogeneousTransgression
import OAI.Analysis.Mahler.HomogeneousTransgressionFTC

namespace OAI

noncomputable section
open Set Filter Metric
open scoped Topology

namespace Mahler

/-- The two independent continuous primitive constructions use the same
ordered slots: alpha, beta, followed by the interleaved d-alpha factors. -/
lemma sourcePrimitiveSlots_eq_primitiveFinEquiv (k : ℕ) :
    sourcePrimitiveSlots k = primitiveFinEquiv k := by
  ext i
  rcases i with i | (i | i)
  · fin_cases i; rfl
  · fin_cases i; rfl
  · rfl

/-- Equality of the actual continuous fields identifies their exterior
 derivatives; no additional integration or regularity premise is introduced. -/
lemma sourceHomogeneousPrimitive_eq_homogeneousPrimitive {k N m : ℕ}
    (G : Fin N → MvPolynomial (Fin (k+2)) ℂ) (t : ℝ) :
    sourceHomogeneousPrimitive (m := m) G t = homogeneousPrimitive (m := m) G t := by
  funext x
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [sourceHomogeneousPrimitive_eq, homogeneousPrimitive_is_wedge]
  unfold sourcePrimitiveFin
  rw [sourcePrimitiveSlots_eq_primitiveFinEquiv]

/-- The homogeneous value and radius-sphere limit in all complex
dimensions at least two, from the mass hypotheses alone. -/
theorem MassHypotheses.homogeneous_flux_endpoints {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G) :
    homogeneousSphereFlux (k+1) N G = (Real.pi*(m:ℝ))^(k+2) ∧
    Tendsto (fun r => (radiusSphereFlux (k+1) (logTau f) r).re)
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(k+2))) := by
  apply h.homogeneousFlux_endpoints_of_transgression
  intro t x hx v hv
  have hn : x ≠ 0 := by intro he; simp [he] at hx
  have ht := h.sphere_residual_transgression hn t v hv
  rwa [← sourceHomogeneousPrimitive_eq_homogeneousPrimitive G t] at ht

/-- The numerical homogeneous flux in every positive complex dimension.
Dimension one is handled by the already proved circle calculation. -/
theorem MassHypotheses.homogeneousSphereFlux_value {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    homogeneousSphereFlux k N G = (Real.pi*(m:ℝ))^(k+1) := by
  cases k with
  | zero => simpa only [Nat.zero_add, pow_one] using h.homogeneousCircle_flux
  | succ k => exact h.homogeneous_flux_endpoints.1

end Mahler

end

end OAI
