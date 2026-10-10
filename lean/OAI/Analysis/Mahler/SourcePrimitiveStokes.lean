import OAI.Analysis.Mahler.HomogeneousPrimitiveRegularity
import OAI.Analysis.Mahler.ExactSphereStokes

namespace OAI

open Complex ContinuousAlternatingMap Set Metric MeasureTheory

noncomputable section
namespace Mahler

/-- C2 on the punctured space follows from the mass hypotheses.
The exact-form flux vanishes in every complex dimension at least two. -/
theorem MassHypotheses.sourceHomogeneousPrimitive_flux_zero {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ) :
    sphereFlux (k+1) (fun x =>
      (extDeriv (sourceHomogeneousPrimitive (m := m) G t) x).toAlternatingMap) = 0 := by
  apply sphereFlux_extDeriv_eq_zero_of_C2 _ isOpen_compl_singleton _
    (h.sourceHomogeneousPrimitive_C2 t)
  intro x hx
  have hn : ‖x‖ = 1 := by simpa using hx
  simpa only [mem_compl_iff, mem_singleton_iff] using
    (show x ≠ 0 from by intro he; simp [he] at hn)

/-- A form agreeing pointwise on sphere tangent tuples with a fixed real scalar
multiple of an exact form has zero sphere flux. -/
theorem sphereFlux_eq_zero_of_tangent_exact_C2 {k : ℕ}
    (B : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→ₗ[ℝ] ℂ)
    (eta : ComplexEuclidean (k+1) → ComplexEuclidean (k+1) [⋀^Fin (2*k)]→L[ℝ] ℂ)
    (c : ℝ) (hreg : ContDiffOn ℝ 2 eta ({0}ᶜ))
    (he : ∀ x, ‖x‖ = 1 → ∀ v : Fin (2*k+1) → ComplexEuclidean (k+1),
      (∀ i, inner ℝ x (v i) = 0) → B x v = (c : ℂ) * extDeriv eta x v) :
    sphereFlux k B = 0 := by
  have hz : sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) = 0 := by
    apply sphereFlux_extDeriv_eq_zero_of_C2 _ isOpen_compl_singleton _ hreg
    intro x hx
    have hn : ‖x‖ = 1 := by simpa using hx
    simpa only [mem_compl_iff, mem_singleton_iff] using
      (show x ≠ 0 from by intro he; simp [he] at hn)
  have hi : sphereFlux k B = c * sphereFlux k (fun x => (extDeriv eta x).toAlternatingMap) := by
    unfold sphereFlux
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    have hx : ‖(x : ComplexEuclidean (k+1))‖ = 1 := by simp
    have hd := orientedDensity_congr_on_tangent hx
      (B := B x) (C := (c : ℂ) • (extDeriv eta x).toAlternatingMap)
      (fun v hv => he x hx v hv)
    rw [hd, orientedDensity_smul]
    simp
  rw [hi, hz, mul_zero]

theorem MassHypotheses.sourcePrimitive_representation_C2 {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ)
    (eta : ComplexEuclidean (k+2) → ComplexEuclidean (k+2) [⋀^Fin (2*(k+1))]→L[ℝ] ℂ)
    (he : ∀ x, (eta x).toAlternatingMap =
      sourcePrimitiveFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x) :
    ContDiffOn ℝ 2 eta ({0}ᶜ) := by
  have hh : eta = sourceHomogeneousPrimitive (m := m) G t := by
    funext x
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    rw [he x, sourceHomogeneousPrimitive_eq]
  rw [hh]
  exact h.sourceHomogeneousPrimitive_C2 t

end Mahler

end

end OAI
