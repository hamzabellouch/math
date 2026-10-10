import OAI.Analysis.Mahler.SpecialSourceMass
import OAI.Analysis.Mahler.HomogeneousTwoFlux

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace Mahler

/-- Eventual equality suffices for the one-sided limit. The zero and
negative-radius branches never enter the statement. -/
theorem MassHypotheses.source_limit_of_radius_identity {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G)
    (hbridge : (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates k) (logTau f) k)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun r => (radiusSphereFlux k (logTau f) r).re)) :
    Tendsto (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0:ℝ)) (𝓝 (homogeneousSphereFlux k N G)) :=
  h.small_sphere_real_flux_limit.congr' hbridge.symm

/-- The homogeneous flux constant is strictly positive under the degree
hypothesis, in every positive complex dimension. -/
theorem MassHypotheses.source_flux_constant_pos {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+1))} {f : Fin N → ComplexEuclidean (k+1) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+1)) ℂ} (h : MassHypotheses (k+1) N m U f G) :
    0 < (Real.pi*(m:ℝ))^(k+1) := by
  have hm : (0:ℝ) < m := by exact_mod_cast (Nat.zero_lt_one.trans_le h.degree_pos)
  exact pow_pos (mul_pos Real.pi_pos hm) _

/-- The dimension-two numerical homogeneous-flux value is determined.
The matching coordinate/radius integral identity is an explicit hypothesis. -/
theorem MassHypotheses.source_two_numeric_limit_of_radius_identity {N m : ℕ}
    {U : Set (ComplexEuclidean 2)} {f : Fin N → ComplexEuclidean 2 → ℂ}
    {G : Fin N → MvPolynomial (Fin 2) ℂ} (h : MassHypotheses 2 N m U f G)
    (hbridge : (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates 1) (logTau f) 1)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun r => (radiusSphereFlux 1 (logTau f) r).re)) :
    Tendsto (fun r => MahlerStokes.sphereFlux r
      (sourceCoordinateForm (sourceCoordinates 1) (logTau f) 1))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^2)) := by
  have ht := h.source_limit_of_radius_identity hbridge
  rwa [h.homogeneousSphereFlux_two_value] at ht

end Mahler
namespace SymmetricMahler

/-- The dimension-two body inequality, conditional on the
coordinate/radius flux identity for special maps.
The flux identity is retained as a hypothesis. -/
theorem symmetric_mahler_two_of_source_radius_identity
    (hbridge : ∀ N (A : Matrix (Fin N) (Fin 2) ℝ),
      Function.Injective (measurement A) → ∀ m : ℕ, 2 ≤ m →
      (fun r => MahlerStokes.sphereFlux r
        (Mahler.sourceCoordinateForm (Mahler.sourceCoordinates 1)
          (Mahler.logTau (euclideanSpecialMap A m)) 1)) =ᶠ[𝓝[>] (0:ℝ)]
        (fun r => (Mahler.radiusSphereFlux 1 (Mahler.logTau (euclideanSpecialMap A m)) r).re))
    {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    8 ≤ (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  have hh := symmetric_mahler_from_special_source_flux_limits 1
    (fun N A hA m hm => (euclideanSpecial_massHypotheses A (by omega) hA hm).source_two_numeric_limit_of_radius_identity (hbridge N A hA m hm)) hK hconv hsym hint
  norm_num at hh
  exact hh

end SymmetricMahler

end

end OAI
