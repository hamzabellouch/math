import OAI.Analysis.Mahler.SourceRegularMass
import OAI.Analysis.Mahler.RegularMassReduction

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SymmetricMahler

/-- The Stokes regularity condition holds for every positive level
of the finite-strip special map. -/
theorem euclideanSpecial_positive_regular_nonzero {n N m : ℕ}
    (A : Matrix (Fin N) (Fin n) ℝ) (hA : Function.Injective (measurement A))
    (hm : 0 < m) {R : ℝ} (hR : 0 < R)
    {z : Mahler.ComplexEuclidean n} (hz : z ∈ euclideanStripDomain A)
    (hlevel : Mahler.tau (euclideanSpecialMap A m) z = R) :
    fderiv ℝ (Mahler.tau (euclideanSpecialMap A m)) z ≠ 0 := by
  intro he
  obtain ⟨v,hv⟩ := euclideanSpecial_positive_regular A hA hm hR hz hlevel (1:ℝ)
  rw [he] at hv
  simp at hv

theorem special_regular_mass_of_source_flux_limit {n N m : ℕ}
    (A : Matrix (Fin N) (Fin (n+1)) ℝ) (hA : Function.Injective (measurement A))
    (hm : 2 ≤ m) (k : ℕ)
    (hlimit : Tendsto
      (fun r => MahlerStokes.sphereFlux r
        (Mahler.sourceCoordinateForm (Mahler.sourceCoordinates n)
          (Mahler.logTau (euclideanSpecialMap A m)) n))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(n+1)))) :
    SpecialRegularMassBound A m k := by
  exact Mahler.source_regular_massBelow_of_flux_limit
    (euclideanSpecial_massHypotheses A (by omega) hA hm)
    (stripRegularLevel_mem k).1 (stripRegularLevel_mem k).2
    (fun z hz he => euclideanSpecial_positive_regular_nonzero A hA (by omega)
      (stripRegularLevel_mem k).1 hz he) hlimit

/-- The arbitrary-body inequality conditional on the numerical coordinate
small-sphere limit. The general-dimensional homogeneous flux
value is retained as a hypothesis. -/
theorem symmetric_mahler_from_special_source_flux_limits (n : ℕ)
    (hlimit : ∀ N (A : Matrix (Fin N) (Fin (n+1)) ℝ),
      Function.Injective (measurement A) → ∀ m : ℕ, 2 ≤ m → Tendsto
      (fun r => MahlerStokes.sphereFlux r
        (Mahler.sourceCoordinateForm (Mahler.sourceCoordinates n)
          (Mahler.logTau (euclideanSpecialMap A m)) n))
      (𝓝[>] (0:ℝ)) (𝓝 ((Real.pi*(m:ℝ))^(n+1))))
    {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ) ≤
      (volume K).toReal*(volume (coordinatePolar K)).toReal := by
  apply symmetric_mahler_from_regular_special_mass (by omega) _ hK hconv hsym hint
  intro N A hA m hm k
  exact special_regular_mass_of_source_flux_limit A hA hm k (hlimit N A hA m hm)

end SymmetricMahler

end

end OAI
