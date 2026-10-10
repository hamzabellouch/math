import OAI.Analysis.PureInfiniteness.JointSpectralPartition
import OAI.Analysis.PureInfiniteness.SpectralSecondMoment

namespace OAI

/-! The sampled square has error at most the square of the mesh size. Together
with the first moment this bounds the concrete return map's Schwarz defect. -/

noncomputable section
open scoped BigOperators ComplexOrder

namespace WeakPureInfiniteness

variable {D I : Type*} [CommCStarAlgebra D] [Fintype I] [DecidableEq I]

def jointGridSquareReconstruction (a : I → D) (r : ℝ) (N : ℤ) (i : I) : D :=
  ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
    (((r * (k i : ℝ)) ^ 2 : ℝ) : ℂ) • productGridHatElement a r _ k

lemma scalarStarHom_squareReconstruction (φ : D →⋆ₐ[ℂ] ℂ) (a : I → D)
    (ha : ∀ i, IsSelfAdjoint (a i)) (r : ℝ) (N : ℤ) (i : I) :
    φ (jointGridSquareReconstruction a r N i) =
      ((r ^ 2 * ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) ^ 2 * productGridHat _ k (fun j => (φ (a j)).re / r) : ℝ) : ℂ) := by
  unfold jointGridSquareReconstruction
  simp only [map_sum, map_smul, scalarStarHom_productGridHat φ a ha]
  rw [Finset.mul_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

lemma norm_jointGridSquareReconstruction_sub_le (a : I → D) (ha : ∀ i, IsSelfAdjoint (a i))
    (r : ℝ) (hr : 0 < r) (N : ℤ)
    (hN : ∀ χ i, 0 ≤ (spectralCharacter χ (a i)).re / r ∧
      (spectralCharacter χ (a i)).re / r ≤ (N : ℝ)) (i : I) :
    ‖a i * a i - jointGridSquareReconstruction a r N i‖ ≤ r ^ 2 := by
  apply norm_le_of_spectralCharacters _ _ (sq_nonneg r)
  intro χ
  let x (j : I) := (spectralCharacter χ (a j)).re / r
  have hp (j : I) : ∑ k ∈ jointGrid (I := I) N j, gridHat k (x j) = 1 :=
    sum_gridHat_eq_one 0 N (x j) (by simpa only [Int.cast_zero] using (hN χ j).1)
      (hN χ j).2
  have hm : ∑ k ∈ jointGrid (I := I) N i, (k : ℝ) ^ 2 * gridHat k (x i) =
      (x i) ^ 2 + (x i - ⌊x i⌋) * (⌊x i⌋ + 1 - x i) :=
    sum_gridHat_second_moment 0 N (x i)
      (by simpa only [Int.cast_zero] using (hN χ i).1) (hN χ i).2
  have hpos (j : I) (k : ℤ) (hk : k ∈ jointGrid (I := I) N j) : (0 : ℤ) ≤ k :=
    (Finset.mem_Icc.mp hk).1
  have hb := joint_spectral_retained_second_moment (jointGrid (I := I) N) x i hp hm hpos
  have he : (spectralCharacter χ (a i)).re ^ 2 -
      r ^ 2 * (∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) ^ 2 * productGridHat _ k x) =
      r ^ 2 * ((x i) ^ 2 - ∑ k : SpectralGridCell (jointGrid (I := I) N) with retainedSpectralCell _ k,
        (k i : ℝ) ^ 2 * productGridHat _ k x) := by
    dsimp only [x]
    field_simp
  rw [map_sub, map_mul, scalarStarHom_squareReconstruction _ a ha,
    scalarStarHom_eq_real _ (ha i)]
  rw [← pow_two, ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [he, abs_mul, abs_of_nonneg (sq_nonneg r)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (sq_nonneg r)

end WeakPureInfiniteness

end

end OAI
