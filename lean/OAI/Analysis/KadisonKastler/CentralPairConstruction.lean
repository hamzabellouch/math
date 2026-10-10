import OAI.Analysis.KadisonKastler.CentralPairFromRankModel
import OAI.Analysis.KadisonKastler.CentralPairCommonSource
import OAI.Analysis.KadisonKastler.CommonRankFactorFibers
import OAI.Analysis.KadisonKastler.CommonCentralGeneration

namespace OAI

/-! # Construction of the common central decomposition

A common source, rank coordinates and bounded-field reconstruction
give the factor fibers of the central decomposition.
-/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity
open scoped IsMulCommutative

noncomputable section

universe u

private theorem concreteCenter_eq (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    concreteCenter M = vonNeumannCenter M := by
  apply VonNeumannAlgebra.ext
  intro T
  rfl

private theorem commutant_le_centralCommutant {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : VonNeumannAlgebra H) :
    M.commutant.toStarSubalgebra ≤ (vonNeumannCenter M).commutant.toStarSubalgebra := by
  intro T hT
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro z hz
  exact VonNeumannAlgebra.mem_commutant_iff.mp hT z hz.1

theorem publishedCentralPairDecomposition : PublishedCentralPairDecomposition.{u} := by
  intro H _ _ _ _ M N hcenter A B C hAc hBc hCc _hAs _hBs hCs hAg hBg hAC hBC hCcentral
  let : IsClosed (A : Set (H →L[ℂ] H)) := hAc
  let : IsClosed (B : Set (H →L[ℂ] H)) := hBc
  let : IsClosed (C : Set (H →L[ℂ] H)) := hCc
  obtain ⟨s⟩ := exists_centralPairCommonSource M N hcenter C hCs hCcentral
  let S := s.source
  let : IsClosed (S : Set (H →L[ℂ] H)) := s.source_closed
  let : TopologicalSpace.SeparableSpace S := s.source_separable
  let : IsClosed (s.leftComm : Set (H →L[ℂ] H)) := s.left_closed
  let : IsClosed (s.rightComm : Set (H →L[ℂ] H)) := s.right_closed
  obtain ⟨Z, hZc, hZs, hZcomm, hZM, hZgen⟩ := exists_separable_central_source M
  let : IsClosed (Z : Set (H →L[ℂ] H)) := hZc
  let : TopologicalSpace.SeparableSpace Z := hZs
  let : IsMulCommutative Z := hZcomm
  let π := Z.subtype
  let D := cyclicDecompositionData π.range
  have hπ : starSubalgebraCommutant π.range = (vonNeumannCenter M).commutant := by
    simpa only [π, subtype_star_range] using hZgen
  have hSN (b : S) (a : Z) : b.val * a.val = a.val * b.val := by
    have ha : a.val ∈ concreteCenter M := by
      rw [concreteCenter_eq H M]
      exact hZM a.property
    exact (VonNeumannAlgebra.mem_commutant_iff.mp (s.central b.property) a.val ha).symm
  let model := borelCommonModel π D S.subtype hSN
  have hAS : A ≤ S := hAC.trans s.original_le
  have hBS : B ≤ S := hBC.trans s.original_le
  let ιA := StarSubalgebra.inclusion hAS
  let ιB := StarSubalgebra.inclusion hBS
  let κM := StarSubalgebra.inclusion s.left_le
  let κN := StarSubalgebra.inclusion s.right_le
  have hAgen : representationVonNeumannAlgebra (S.subtype.comp ιA) = M := by
    change representationVonNeumannAlgebra A.subtype = M
    rw [representationVonNeumannAlgebra_eq_generated, subtype_star_range, hAg]
  have hBgen : representationVonNeumannAlgebra (S.subtype.comp ιB) = N := by
    change representationVonNeumannAlgebra B.subtype = N
    rw [representationVonNeumannAlgebra_eq_generated, subtype_star_range, hBg]
  have hLgen : representationVonNeumannAlgebra (S.subtype.comp κM) = M.commutant := by
    change (starSubalgebraCommutant s.leftComm.subtype.range).commutant = M.commutant
    rw [subtype_star_range]
    exact s.left_generates
  have hRgen : representationVonNeumannAlgebra (S.subtype.comp κN) = N.commutant := by
    change (starSubalgebraCommutant s.rightComm.subtype.range).commutant = N.commutant
    rw [subtype_star_range]
    exact s.right_generates
  have hAM : A ≤ M.toStarSubalgebra := by
    intro T hT
    rw [← hAg]
    exact subset_generatedVonNeumannAlgebra A hT
  have hBN : B ≤ N.toStarSubalgebra := by
    intro T hT
    rw [← hBg]
    exact subset_generatedVonNeumannAlgebra B hT
  have hAL (a : A) (c : s.leftComm) : a.val * c.val = c.val * a.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp (s.left_mem c.property) a.val (hAM a.property)
  have hBR (b : B) (c : s.rightComm) : b.val * c.val = c.val * b.val :=
    VonNeumannAlgebra.mem_commutant_iff.mp (s.right_mem c.property) b.val (hBN b.property)
  have hMc : M.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ]
    exact le_center_commutant M
  have hM'c : M.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ]
    exact commutant_le_centralCommutant M
  have hcenters : vonNeumannCenter M = vonNeumannCenter N := by
    simpa only [concreteCenter_eq] using hcenter
  have hNc : N.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ, hcenters]
    exact le_center_commutant N
  have hN'c : N.commutant.toStarSubalgebra ≤ (starSubalgebraCommutant π.range).toStarSubalgebra := by
    rw [hπ, hcenters]
    exact commutant_le_centralCommutant N
  obtain ⟨Q, hQ, hQf⟩ := commonRank_algebra_decomposition model ιA κM M hAgen hLgen hMc hM'c
    (fun a c => Subtype.ext (hAL a c))
  obtain ⟨R, hR, hRf⟩ := commonRank_algebra_decomposition model ιB κN N hBgen hRgen hNc hN'c
    (fun b c => Subtype.ext (hBR b c))
  have hAj : representationVonNeumannAlgebra (jointCStarSource A s.leftComm).subtype =
      starSubalgebraCommutant π.range := by
    exact (representation_joint_eq_center_commutant M A s.leftComm hAg s.left_generates
      hAM s.left_mem).trans hπ.symm
  have hBj : representationVonNeumannAlgebra (jointCStarSource B s.rightComm).subtype =
      starSubalgebraCommutant π.range := by
    rw [hπ, hcenters]
    exact representation_joint_eq_center_commutant N B s.rightComm hBg s.right_generates
      hBN s.right_mem
  apply centralPairDecomposition_of_rankModel M N A B C S model hAC hBC s.original_le
    Q R hQ hR hQf hRf
  intro n
  have ha := commonRank_factor_fibers S model A s.leftComm hAS s.left_le hAL hAj n
  have hb := commonRank_factor_fibers S model B s.rightComm hBS s.right_le hBR hBj n
  filter_upwards [ha, hb] with x hx hy
  exact ⟨hx, hy⟩

end

end KadisonKastler

end OAI
