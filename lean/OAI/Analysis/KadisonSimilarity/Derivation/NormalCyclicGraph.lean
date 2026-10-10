import OAI.Analysis.KadisonSimilarity.Representation.NormalSpectralTruncation
import OAI.Analysis.KadisonSimilarity.Derivation.CyclicGraphSequences

namespace OAI

/-! A faithful normal finite trace makes the cyclic orbit map closable.
The proof removes a high spectral projection of vanishing trace, leaving
an arbitrarily small operator applied to the fixed cyclic vector. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology ComplexOrder

variable {H K E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance normalCyclic_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  change IsClosed M.carrier
  rw [← M.centralizer_centralizer']
  exact Set.isClosed_centralizer _

theorem normal_tracial_cyclic_graph_closable
    (M : VonNeumannAlgebra H) (G : TracialCornerGeometry M.toStarSubalgebra E)
    (τ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hτ : ∀ a, τ a = G.trace a)
    (h1 : G.trace 1 = 1) (hf : Function.Injective G.vector)
    (N : VonNeumannAlgebra E) (hN : G.left.range = N.toStarSubalgebra)
    (ρ : M.toStarSubalgebra →⋆ₐ[ℂ] (K →L[ℂ] K)) (J : K →ₗᵢ[ℂ] H)
    (hJ : ∀ a, J.toContinuousLinearMap.comp (ρ a) =
      (a : H →L[ℂ] H).comp J.toContinuousLinearMap) (ξ : K)
    (x : cyclicGraph G.left ρ (G.vector 1) ξ)
    (hx : (x : RectangularSum E K).fst = 0) :
    (x : RectangularSum E K).snd = 0 := by
  obtain ⟨a, hs, ht⟩ := exists_cyclicGraph_coordinate_limits G.left ρ (G.vector 1) ξ x
  have hsource : Tendsto (fun n => G.vector (a n)) atTop (𝓝 0) := by
    simpa only [G.left_vector, mul_one, hx] using hs
  have htarget : Tendsto (fun n => (a n : H →L[ℂ] H) (J ξ)) atTop
      (𝓝 (J (x : RectangularSum E K).snd)) := by
    have h := (J.continuous.tendsto (x : RectangularSum E K).snd).comp ht
    have he (n : ℕ) : J (ρ (a n) ξ) = (a n : H →L[ℂ] H) (J ξ) :=
      congrArg (fun T : K →L[ℂ] H => T ξ) (hJ (a n))
    exact h.congr (fun n => he n)
  have hy := normal_geometry_orbit_limit_eq_zero M G τ hτ h1 hf N hN a hsource
    (J ξ) (J (x : RectangularSum E K).snd) htarget
  exact J.injective (hy.trans (map_zero J).symm)

end KadisonSimilarity

end

end OAI
