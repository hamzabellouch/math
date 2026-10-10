import OAI.Geometry.CylinderCovering.Singular.EdgeOneDifferentialDefinitions

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace SingularEdgeOne
open RuledApproximation

structure DictionaryStatement : Prop where
  field_components : ∀ (p w l : ℝ), 0 < l →
    edgeU p w l = fieldP p (2 * w) l / 4 ∧
    edgeV p w l = fieldQ p (2 * w) l / 2
  hamiltonian : ∀ (p w l : ℝ), 0 < l →
    edgeField p (vec2 w l) =
      vec2 (-deriv (fun r : ℝ => edgeHamiltonian p w r) l)
        (deriv (fun v : ℝ => edgeHamiltonian p v l) w)
  ceiling_formula : ∀ (p w c : ℝ),
    edgeCeiling p w = w ^ 2 * edgeU p w (1 / 2) ∧
    c ^ 2 * ceiling p (2 * w) = (4 * c) ^ 2 * edgeCeiling p w
  physical_energy : ∀ (p w c l : ℝ), 0 < l →
    (4 * c) ^ 2 *
      (edgeU p w l ^ 2 + (1 / Real.sqrt 2 : ℝ) ^ 2 * edgeV p w l ^ 2) =
      c ^ 2 * (fieldP p (2 * w) l ^ 2 + 2 * fieldQ p (2 * w) l ^ 2)
  tetrahedron_image : physicalSimilarity '' tetrahedron = edgeTetrahedron
  lower_image : ∀ (p c : ℝ) (D : Set Plane), (∀ b ∈ D, 0 < b 1) →
    physicalSimilarity '' physicalRuled (Real.sqrt 2) D
      (fun b => c • singularField p b) 1 = edgeLower p (4 * c) (labelMap '' D)
  upper_image : ∀ (p c : ℝ) (D : Set Plane), (∀ b ∈ D, 0 < b 1) →
    physicalSimilarity '' upperSegments p c D = edgeUpper p (4 * c) (labelMap '' D)
  physical_cost : ∀ (p c : ℝ) (D : Set Plane), MeasurableSet D → (∀ z ∈ D, 0 < z 1) →
    (1 / Real.sqrt 2) *
      (∫ z in labelMap '' D, physicalWeight (1 / Real.sqrt 2) ((4 * c) • edgeField p z)) =
      (Real.sqrt 2 * (∫ z in D, physicalWeight (Real.sqrt 2) (c • singularField p z))) / 4
  derivative_conjugacy : ∀ (p c : ℝ) (z : Plane), 0 < z 1 →
    ((4 * c) / 2) • fderiv ℝ (edgeField p) (labelMap z) =
      c • labelContinuous.toContinuousLinearMap.comp
        ((fderiv ℝ (singularField p) z).comp labelContinuous.symm.toContinuousLinearMap)
  spectral_conjugacy : ∀ (p c mu : ℝ) (z : Plane), 0 < z 1 →
    (Module.End.HasEigenvalue
      (((4 * c) / 2) • fderiv ℝ (edgeField p) (labelMap z)).toLinearMap mu ↔
      Module.End.HasEigenvalue ((c • fderiv ℝ (singularField p) z).toLinearMap) mu)
  exact_parameters : ∀ (k gamma : ℝ), 0 ≤ k →
    (k / 4) ^ gamma = (4 : ℝ) ^ (-gamma) * k ^ gamma ∧
    (k / 4) ^ (5 / 2 : ℝ) = k ^ (5 / 2 : ℝ) / 32
  boundary_integral : ∀ p : ℝ,
    (∫ w in (-1 / 4 : ℝ)..(1 / 4 : ℝ), edgeCeiling p w) = edgeA p
  energy_integral : ∀ p : ℝ, 1 < p →
    (∫ z in edgeDomain0, edgeEnergy p (z 0) (z 1)) = edgeG p
  coefficient_formula : ∀ p : ℝ, p ≠ 0 →
    edgeA p - edgeG p = (2 * p ^ 2 + 10 * p - 13) / (15360 * p) ∧
    edgeA p - edgeG p = coefficient p / 32
  coefficient_negative : ∀ p : ℝ, 1 < p → p < (Real.sqrt 51 - 5) / 2 →
    edgeA p - edgeG p < 0
  coefficient_limits :
    Tendsto edgeA (𝓝 1) (𝓝 (16 / 15360)) ∧
    Tendsto edgeG (𝓝 1) (𝓝 (17 / 15360))

end SingularEdgeOne

end

end OAI
