import OAI.Analysis.KadisonKastler.CompleteCommutantDistance

namespace OAI

/-! # Commutant distance for paired representations

This is the exact two-by-two specialization used by the stability proof.
The general represented estimate is transported through the faithful
finite Hilbert-sum matrix representation, preserving its constant.
-/

namespace KadisonKastler

noncomputable section

variable (A K : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

local instance blockDistanceBaseOrder : PartialOrder (K →L[ℂ] K) := CStarAlgebra.spectralOrder _
local instance blockDistanceBaseStarOrder : StarOrderedRing (K →L[ℂ] K) :=
  CStarAlgebra.spectralOrderedRing _

/-- Arveson--Christensen commutant distance for a pair of representations. -/
theorem publishedBlockCommutantApproximation : PublishedBlockCommutantApproximation A K := by
  intro π T e he hcb r hr
  let H := Generator.FiniteHilbert (Fin 2) K
  let φ : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
    hilbertMatrixHom
  let ρ := φ.comp π
  have hid : (innerDerivation (φ T)).comp ρ.toAlgHom.toLinearMap =
      φ.toAlgHom.toLinearMap.comp ((innerDerivation T).comp π.toAlgHom.toLinearMap) := by
    apply LinearMap.ext
    intro a
    change φ T * φ (π a) - φ (π a) * φ T = φ (T * π a - π a * T)
    rw [map_sub, map_mul, map_mul]
  have hc : CompletelyBoundedBy ((innerDerivation (φ T)).comp ρ.toAlgHom.toLinearMap) e := by
    rw [hid]
    intro p q X
    rw [matrix_map_comp,
      injective_starAlgHom_completelyIsometric φ hilbertMatrixHom_injective p q]
    exact hcb p q X
  obtain ⟨D, hD, hn⟩ := exists_commutant_of_completelyBounded ρ (φ T) he hc hr
  let B : CStarMatrix (Fin 2) (Fin 2) (K →L[ℂ] K) :=
    CStarMatrix.ofMatrix (fun i j => Generator.operatorEntry D i j)
  have hB : φ B = D := hilbertMatrix_operatorEntries D
  refine ⟨B, ?_, ?_⟩
  · intro a
    apply hilbertMatrixHom_injective
    change φ (B * π a) = φ (π a * B)
    rw [map_mul, map_mul, hB]
    exact hD a
  · rw [← norm_hilbertMatrix]
    change ‖φ (B - T)‖ < r
    rw [map_sub, hB]
    exact hn

end

end KadisonKastler

end OAI
