import OAI.Analysis.KadisonKastler.ConstructedMatrixPositionStability
import OAI.Analysis.KadisonKastler.ConstructedFiniteFactorModulus
import OAI.Analysis.KadisonKastler.OriginalMatrixInjectivity
import OAI.Analysis.KadisonKastler.PublishedFiniteType
import OAI.Analysis.KadisonKastler.TracialUltrapowerConstruction
import OAI.Analysis.KadisonKastler.FiniteMatrixUltraproductConstruction
import OAI.Analysis.KadisonKastler.DiagonalFockConstruction
import OAI.Analysis.KadisonKastler.BlockCommutantConstruction

namespace OAI

/-! # Uniform strong stability of separably acting II₁ factors

Boundary means, field projections and finite type stability combine
with a common tracial position and uniform amplification to give a
small spatial implementation.
-/

namespace KadisonKastler

noncomputable section

universe u

local instance applicationFactorOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    PartialOrder (Algebra P) := CStarAlgebra.spectralOrder _

local instance applicationFactorStarOrder {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (P : VonNeumannAlgebra K) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

/-- The published specializations used for the finite-factor application.
Each field refers to a separately documented published input. -/
structure FiniteFactorPublishedInputs : Prop where
  boundary : PublishedBoundary.{u}
  tomiyama : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H], PublishedFieldTomiyamaFamily H
  finiteType : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H], PublishedFiniteType (H := H)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M N : VonNeumannAlgebra H}

/-- The neighbor need not be given as a finite factor, and the original
representation need not have a tracial vector. -/
theorem finiteFactor_spatial_of_published (h : FiniteFactorPublishedInputs.{u})
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {t : ℝ} (ht : 0 < t) (_htEmbed : t < 1 / 100)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 4000000) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ constructedFiniteFactorError t := by
  have hN := isII1Factor_of_near_of_published (h.finiteType H) hM
    (hgap.trans (by linarith : t < 1 / 10))
  obtain ⟨A, hA, _, hirr⟩ := exists_original_irreducible_matrix_algebra hM
  exact constructed_finiteFactor_spatial_of_matrixStages_and_boundary
    h.boundary h.tomiyama hM hN A hA hirr
    ht htPosition hgap htStandard htSpatial

/-- The tolerance is uniform in the factors, their representations and the
separable ambient Hilbert space. This is the finite-factor part of the paper. -/
theorem uniform_II1_strong_stability (h : FiniteFactorPublishedInputs.{u})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (M N : VonNeumannAlgebra H), Generator.IsII1Factor M.toStarSubalgebra →
      kkDistance M N < δ → NearConjugacy M N ε := by
  obtain ⟨t, ht, he, hp, hs, hc, herror⟩ := exists_constructed_finiteFactor_tolerance hε
  refine ⟨t, ht, ?_⟩
  intro H _ _ _ _ M N hM hgap
  obtain ⟨u, hu, hnorm⟩ := finiteFactor_spatial_of_published h hM ht he hp hgap hs hc
  exact ⟨u, hu, hnorm.trans_lt herror⟩

end

end KadisonKastler

end OAI
