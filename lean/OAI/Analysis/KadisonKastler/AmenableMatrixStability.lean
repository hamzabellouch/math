import OAI.Analysis.KadisonKastler.SemifiniteCornerStability
import OAI.Analysis.KadisonKastler.ConjugateFactor
import OAI.Analysis.KadisonKastler.FullCornerPreparation

namespace OAI

/-! # Removing the common matrix-unit hypothesis

A countable full matrix corner in an injective subalgebra is moved into the
neighbor using the constructed finite-group embedding. The original
finite corner and its representation remain fixed throughout this step.
-/

namespace KadisonKastler

open Filter Topology

noncomputable section

universe u

/-- The displacement from the injective embedding followed by the finite
corner conjugacy. -/
def matrixCornerError (t : ℝ) : ℝ := 150 * t + constructedFiniteFactorError (302 * t)

theorem continuous_matrixCornerError : Continuous matrixCornerError := by
  unfold matrixCornerError
  exact (continuous_const.mul continuous_id).add
    (continuous_constructedFiniteFactorError.comp (continuous_const.mul continuous_id))

@[simp] theorem matrixCornerError_zero : matrixCornerError 0 = 0 := by
  simp [matrixCornerError]

theorem matrixCornerError_monotone : Monotone matrixCornerError := by
  intro a b hab
  exact add_le_add (mul_le_mul_of_nonneg_left hab (by norm_num))
    (constructedFiniteFactorError_monotone (mul_le_mul_of_nonneg_left hab (by norm_num)))

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- A nearby algebra need not already contain the matrix units. The
constructed matrix embedding creates this common position, after which compression
and the proved inflation theorem provide the whole-space conjugacy. -/
theorem spatial_of_injective_matrix_subalgebra
    (h : FiniteFactorPublishedInputs.{u})
    (M N S : VonNeumannAlgebra H) (hSM : S ≤ M) (_hS : IsInjective S)
    (hFS : ∀ i j, F.entry i j ∈ S)
    (hCorner : Generator.IsII1Factor
      (representedCorner E M (F.zero_zero ▸ hSM (hFS 0 0))).toStarSubalgebra)
    {t : ℝ} (ht : 0 < t) (htEmbed : 302 * t < 1 / 100)
    (htPosition : 302 * (302 * t) < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * (302 * t)) < 1 / 100000)
    (htSpatial : commonPositionError (302 * (302 * t)) < 1 / 4000000) :
    ∃ u : unitary (H →L[ℂ] H), Conjugates u M N ∧
      ‖(u : H →L[ℂ] H) - 1‖ ≤ matrixCornerError t := by
  obtain ⟨w, hw, hFP, hnear⟩ := F.exists_common_neighbor M N
    (fun i j => hSM (hFS i j)) (by linarith) hgap
  let P := unitaryConjugateAlgebra (star w) N
  have hFM (i j : ℕ) : F.entry i j ∈ M := hSM (hFS i j)
  have hgapP : kkDistance M P < 302 * t := by
    change kkDistance M (unitaryConjugateAlgebra (star w) N) < _
    linarith
  obtain ⟨v, hv, hnorm⟩ := F.spatial_of_common_entries h M P hFM hFP
    hCorner (by positivity) htEmbed htPosition hgapP htStandard htSpatial
  refine ⟨w * v, conjugates_of_conjugated_neighbor w v hv, ?_⟩
  exact (conjugated_neighbor_displacement_le w v).trans (add_le_add hw hnorm)

end FullMatrixCorner

/-- Uniform strong stability when the source has an injective matrix
subalgebra with a finite-factor initial corner. The matrix subalgebra is
not required to lie in the neighbor. -/
theorem uniform_strong_stability_of_injective_matrix_subalgebra
    (h : FiniteFactorPublishedInputs.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (E : Submodule ℂ H) [CompleteSpace E] (F : FullMatrixCorner E)
      (M N S : VonNeumannAlgebra H) (hSM : S ≤ M), IsInjective S →
      ∀ hFS : ∀ i j, F.entry i j ∈ S,
      Generator.IsII1Factor
        (representedCorner E M (F.zero_zero ▸ hSM (hFS 0 0))).toStarSubalgebra →
      kkDistance M N < t → NearConjugacy M N ε := by
  obtain ⟨δ, hδ, hstable⟩ := uniform_strong_stability_of_common_matrix_entries h
    (half_pos hε)
  let t := min (δ / 604) (min (ε / 600) (1 / 2000))
  have ht : 0 < t := lt_min (by positivity) (lt_min (by positivity) (by norm_num))
  have htδ : t ≤ δ / 604 := min_le_left _ _
  have htε : t ≤ ε / 600 := (min_le_right _ _).trans (min_le_left _ _)
  have htSmall : t ≤ 1 / 2000 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨t, ht, ?_⟩
  intro H _ _ _ _ E _ F M N S hSM _hS hFS hCorner hgap
  obtain ⟨w, hw, hFP, hnear⟩ := F.exists_common_neighbor M N
    (fun i j => hSM (hFS i j)) (by linarith) hgap
  let P := unitaryConjugateAlgebra (star w) N
  have hFM (i j : ℕ) : F.entry i j ∈ M := hSM (hFS i j)
  have hgapP : kkDistance M P < δ := by
    change kkDistance M (unitaryConjugateAlgebra (star w) N) < _
    linarith
  obtain ⟨v, hv, hnorm⟩ := hstable H E F M P hFM hFP hCorner hgapP
  refine ⟨w * v, conjugates_of_conjugated_neighbor w v hv, ?_⟩
  have hn := conjugated_neighbor_displacement_le w v
  linarith

end

end KadisonKastler

end OAI
