import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFiniteRankEigen

namespace OAI

/-! # Canonical finite-dimensional factor of the actual finite-rank remainder

The factor space is the range of the remainder already constructed from
the evolution. No auxiliary factorization or spectral hypothesis is needed.
-/

open Filter Topology Bornology

namespace DefocusingNLS

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

noncomputable def finiteRankRangeMap (K : E →L[ℂ] E) :
    E →L[ℂ] LinearMap.range K.toLinearMap :=
  K.codRestrict (LinearMap.range K.toLinearMap) (fun x => ⟨x, rfl⟩)

omit [CompleteSpace E] in
theorem finiteRank_range_factorization (K : E →L[ℂ] E) :
    (LinearMap.range K.toLinearMap).subtypeL.comp (finiteRankRangeMap K) = K := by
  ext x
  rfl

noncomputable def finiteRankSchurDet (B K : E →L[ℂ] E) (z : ℂ) : ℂ :=
  (ContinuousLinearMap.id ℂ (LinearMap.range K.toLinearMap) -
    (finiteRankRangeMap K).comp
      ((resolvent B z).comp (LinearMap.range K.toLinearMap).subtypeL)).det

theorem finiteRankSchurDet_analyticAt (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (z : ℂ) (hz : z ∈ resolventSet ℂ B) :
    AnalyticAt ℂ (finiteRankSchurDet B K) z := by
  let : FiniteDimensional ℂ (LinearMap.range K.toLinearMap) := hK
  exact finiteRank_determinant_analyticAt B
    (LinearMap.range K.toLinearMap).subtypeL (finiteRankRangeMap K) z hz

theorem finiteRankSchurDet_tendsto_one (B K : E →L[ℂ] E) :
    Tendsto (finiteRankSchurDet B K) (cobounded ℂ) (𝓝 1) := by
  exact finiteRank_determinant_tendsto_one B
    (LinearMap.range K.toLinearMap).subtypeL (finiteRankRangeMap K)

theorem finiteRankSchurDet_spectrum_iff (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (z : ℂ) (hz : z ∈ resolventSet ℂ B) :
    z ∈ spectrum ℂ (B + K) ↔ finiteRankSchurDet B K z = 0 := by
  let : FiniteDimensional ℂ (LinearMap.range K.toLinearMap) := hK
  simpa only [finiteRank_range_factorization, finiteRankSchurDet] using
    finiteRank_spectrum_iff_det_zero B (LinearMap.range K.toLinearMap).subtypeL
      (finiteRankRangeMap K) z hz

omit [CompleteSpace E] in
theorem finiteRankSchurDet_exists_eigenvector (B K : E →L[ℂ] E)
    (hK : FiniteDimensional ℂ (LinearMap.range K.toLinearMap))
    (z : ℂ) (hz : z ∈ resolventSet ℂ B) (hdet : finiteRankSchurDet B K z = 0) :
    ∃ x : E, x ≠ 0 ∧ (B + K) x = z • x := by
  let : FiniteDimensional ℂ (LinearMap.range K.toLinearMap) := hK
  simpa only [finiteRank_range_factorization] using
    finiteRank_exists_eigenvector_of_det_zero B (LinearMap.range K.toLinearMap).subtypeL
      (finiteRankRangeMap K) z hz hdet

end

end DefocusingNLS

end OAI
