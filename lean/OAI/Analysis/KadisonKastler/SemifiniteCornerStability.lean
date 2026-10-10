import OAI.Analysis.KadisonKastler.InflatedConjugacy
import OAI.Analysis.KadisonKastler.FiniteFactorApplication

namespace OAI

/-! # Stability from a common countable matrix decomposition

Compression does not enlarge the distance, and the corner conjugacy inflates
through the actual matrix units without enlarging its displacement. Only
the initial corner is assumed to be a II₁ factor.
-/

namespace KadisonKastler

noncomputable section

universe u

namespace FullMatrixCorner

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {E : Submodule ℂ H} [CompleteSpace E]
  (F : FullMatrixCorner E)

/-- The quantitative finite-factor estimate survives the common countable
matrix decomposition, with exactly the same displacement bound. -/
theorem spatial_of_common_entries (h : FiniteFactorPublishedInputs.{u})
    (M N : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N)
    (hCorner : Generator.IsII1Factor
      (representedCorner E M (F.zero_zero ▸ hM 0 0)).toStarSubalgebra)
    {t : ℝ} (ht : 0 < t) (htEmbed : t < 1 / 100)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 4000000) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ constructedFiniteFactorError t := by
  have hgapCorner :
      kkDistance (representedCorner E M (F.zero_zero ▸ hM 0 0))
        (representedCorner E N (F.zero_zero ▸ hN 0 0)) < t :=
    (kkDistance_representedCorner_le E M N _ _).trans_lt hgap
  obtain ⟨v, hv, hnorm⟩ := finiteFactor_spatial_of_published h hCorner
    ht htEmbed htPosition hgapCorner htStandard htSpatial
  exact ⟨F.inflateUnitary v, F.conjugates_inflateUnitary M N hM hN v hv,
    (F.norm_inflateUnitary_sub_one_le v).trans hnorm⟩

/-- Either of the two initial corners may be the given II₁ factor. -/
theorem spatial_of_common_entries_right (h : FiniteFactorPublishedInputs.{u})
    (M N : VonNeumannAlgebra H)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N)
    (hCorner : Generator.IsII1Factor
      (representedCorner E N (F.zero_zero ▸ hN 0 0)).toStarSubalgebra)
    {t : ℝ} (ht : 0 < t) (htEmbed : t < 1 / 100)
    (htPosition : 302 * t < 174 / 1000000000000000)
    (hgap : kkDistance M N < t)
    (htStandard : 3 * 50948 * Real.sqrt (302 * t) < 1 / 100000)
    (htSpatial : commonPositionError (302 * t) < 1 / 4000000) :
    ∃ v : unitary (H →L[ℂ] H), Conjugates v M N ∧
      ‖(v : H →L[ℂ] H) - 1‖ ≤ constructedFiniteFactorError t := by
  obtain ⟨v, hv, hn⟩ := F.spatial_of_common_entries h N M hN hM hCorner
    ht htEmbed htPosition (by simpa only [kkDistance_comm] using hgap) htStandard htSpatial
  refine ⟨star v, hv.symm, ?_⟩
  have he : ‖(star v : H →L[ℂ] H) - 1‖ = ‖(v : H →L[ℂ] H) - 1‖ := by
    simpa only [Unitary.coe_star, star_sub, star_one] using
      norm_star ((v : H →L[ℂ] H) - 1)
  exact he ▸ hn

end FullMatrixCorner

/-- The same uniform tolerance as in the finite-factor theorem applies to
all separably acting algebras with this common matrix decomposition. -/
theorem uniform_strong_stability_of_common_matrix_entries
    (h : FiniteFactorPublishedInputs.{u}) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
      (E : Submodule ℂ H) [CompleteSpace E] (F : FullMatrixCorner E)
      (M N : VonNeumannAlgebra H)
      (hM : ∀ i j, F.entry i j ∈ M) (_hN : ∀ i j, F.entry i j ∈ N),
      Generator.IsII1Factor
        (representedCorner E M (F.zero_zero ▸ hM 0 0)).toStarSubalgebra →
      kkDistance M N < δ → NearConjugacy M N ε := by
  obtain ⟨δ, hδ, hstability⟩ := uniform_II1_strong_stability h hε
  refine ⟨δ, hδ, ?_⟩
  intro H _ _ _ _ E _ F M N hM hN hCorner hgap
  have hgapCorner :
      kkDistance (representedCorner E M (F.zero_zero ▸ hM 0 0))
        (representedCorner E N (F.zero_zero ▸ hN 0 0)) < δ :=
    (kkDistance_representedCorner_le E M N _ _).trans_lt hgap
  obtain ⟨v, hv, hnorm⟩ := hstability E _ _ hCorner hgapCorner
  exact ⟨F.inflateUnitary v, F.conjugates_inflateUnitary M N hM hN v hv,
    (F.norm_inflateUnitary_sub_one_le v).trans_lt hnorm⟩

end

end KadisonKastler

end OAI
