import OAI.Analysis.KadisonKastler.CommonPositionFiniteIsomorphism
import OAI.Analysis.KadisonKastler.FiniteFactorSpatial

namespace OAI

/-! # Spatial stability after a common injective subfactor is fixed

The published change of representation, the constructed boundary
isomorphism and the actual paired-factor amplification are joined here.
The unitary acts on the original Hilbert space.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M N R : VonNeumannAlgebra H}

local instance commonFactorOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _

local instance commonFactorStarOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

local instance commonOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _

local instance commonOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- Explicit common-position error after returning to the original space. -/
def commonPositionError (g : ℝ) : ℝ := 1135 * 50948 * Real.sqrt g + 2 * g

/-- Nearby II₁ factors with a common irreducible injective subalgebra are
conjugate on the original space, with an explicit square-root bound. -/
theorem common_subfactor_spatial_stability
    (hPosition : PublishedCommonTracialPosition.{u})
    (hBoundary : PublishedBoundary.{u})
    (hTom : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] [TopologicalSpace.SeparableSpace K], PublishedFieldTomiyamaFamily K)
    (hpub : PublishedTracialUltrapower.{u})
    (hmat : PublishedFiniteMatrixUltraproduct)
    (hind : PublishedPopaFiniteBaseIndependence.{u})
    (hFock : PublishedDiagonalFockRepresentation.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (hCyclic : ∀ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      PublishedCyclicSimilarity.{u, u} (A := Algebra (pairedVonNeumann hM hN θ)))
    (hCommutant : PublishedBlockCommutantApproximation (Algebra M) H)
    (hRM : R ≤ M) (hRN : R ≤ N) (hR : IsInjective R)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    {g : ℝ} (hg : 0 < g) (hgp : g < 174 / 1000000000000000)
    (hgap : kkDistance M N < g)
    (hstandard : 3 * 50948 * Real.sqrt g < 1 / 100000)
    (hspatial : commonPositionError g < 1 / 2400) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ 2400 * commonPositionError g := by
  obtain ⟨K, hK, hKi, hKc, hKs, hd⟩ := hPosition H M N R hRM hRN hM hN hR hirr
    g hg hgp (nearInclusion_of_kkDistance_lt hgap)
    (nearInclusion_of_kkDistance_lt (by rwa [kkDistance_comm]))
  let : NormedAddCommGroup K := hK
  let : InnerProductSpace ℂ K := hKi
  let : CompleteSpace K := hKc
  let : TopologicalSpace.SeparableSpace K := hKs
  obtain ⟨d⟩ := hd
  have hsqrt : 0 < Real.sqrt g := Real.sqrt_pos.2 hg
  have hb : 2 * d.tolerance < 3 * 50948 * Real.sqrt g := by
    nlinarith only [d.tolerance_lt, hsqrt]
  obtain ⟨θ, hθ⟩ := d.exists_finiteFactor_isomorphism hBoundary (hTom K) hM hN hirr
    hgap hb hstandard
  have he : 0 ≤ commonPositionError g := by unfold commonPositionError; positivity
  have hθ' (x : Algebra M) :
      ‖(x : H →L[ℂ] H) - (θ x : H →L[ℂ] H)‖ ≤ commonPositionError g * ‖x‖ := by
    rw [norm_sub_rev]
    apply (hθ x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    unfold commonPositionError
    nlinarith only [d.tolerance_lt]
  exact finiteFactor_spatial_of_near_starEquiv hpub hmat hind hFock hM hN θ
    (hCyclic θ) hCommutant he hspatial hθ'

end

end KadisonKastler

end OAI
