import OAI.Analysis.PureInfiniteness.JointSpectralPartition

namespace OAI

/-! The mesh-independent square-error estimate for the sampled spectral row.
It is the norm estimate needed before the fixed-cut diagonalization in KR02
Remark 7.5 and Lemma 7.6. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

def sampledQuadraticError {B : Type*} [NonUnitalCStarAlgebra B] (a f : B) (t : ℝ) : B :=
  a * a * f - ((2 * t : ℝ) : ℂ) • (a * f) + ((t ^ 2 : ℝ) : ℂ) • f

lemma map_sampledQuadraticError {B C : Type*}
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    (φ : B →⋆ₙₐ[ℂ] C) (a f : B) (t : ℝ) :
    φ (sampledQuadraticError a f t) = sampledQuadraticError (φ a) (φ f) t := by
  simp only [sampledQuadraticError, map_add, map_sub, map_mul, map_smul]

variable {D I : Type*} [CommCStarAlgebra D] [Fintype I] [DecidableEq I]

lemma scalarStarHom_sampledQuadraticError (φ : D →⋆ₐ[ℂ] ℂ) (a f : D)
    (ha : IsSelfAdjoint a) (u t : ℝ) (hf : φ f = (u : ℂ)) :
    φ (sampledQuadraticError a f t) = (((φ a).re - t) ^ 2 * u : ℝ) := by
  unfold sampledQuadraticError
  simp only [map_add, map_sub, map_mul, map_smul, smul_eq_mul, hf]
  rw [scalarStarHom_eq_real φ ha]
  push_cast
  simp only [Complex.ofReal_re]
  ring

lemma norm_sum_sampledQuadraticError_le (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (hr : 0 < r)
    (s : I → Finset ℤ) (T : Finset (SpectralGridCell s)) (i : I) :
    ‖∑ k ∈ T, sampledQuadraticError (a i) (productGridPlateauElement a r s k)
      (r * (k i : ℝ))‖ ≤ 4 * r ^ 2 * (5 : ℝ) ^ Fintype.card I := by
  apply norm_le_of_spectralCharacters _ _ (by positivity)
  intro χ
  let x (j : I) := (spectralCharacter χ (a j)).re / r
  have hs (k : SpectralGridCell s) :
      spectralCharacter χ (sampledQuadraticError (a i) (productGridPlateauElement a r s k)
        (r * (k i : ℝ))) =
      ((r ^ 2 * ((x i - (k i : ℝ)) ^ 2 * productGridPlateau s k x) : ℝ) : ℂ) := by
    rw [scalarStarHom_sampledQuadraticError _ _ _ (ha i) _ _
      (scalarStarHom_productGridPlateau _ a ha r s k)]
    congr 1
    dsimp only [x]
    field_simp
  rw [map_sum]
  simp_rw [hs]
  rw [← Complex.ofReal_sum, ← Finset.mul_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (sq_nonneg r)]
  have hsum : 0 ≤ ∑ k ∈ T, (x i - (k i : ℝ)) ^ 2 * productGridPlateau s k x :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (sq_nonneg _)
      (productGridPlateau_bounds s k x).1)
  rw [abs_of_nonneg hsum]
  have hbound := mul_le_mul_of_nonneg_left
    (sum_productGridPlateau_coordinate_sq_le s x i T) (sq_nonneg r)
  nlinarith

end WeakPureInfiniteness

end

end OAI
