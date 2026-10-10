import OAI.Analysis.KadisonKastler.MatrixNearInclusion
import OAI.Analysis.KadisonKastler.MatrixCommutantDistance
import OAI.Analysis.KadisonKastler.NearInclusionDistance

namespace OAI

/-! # Commutant estimates from individual matrix approximants

A matrix approximant from `N` commutes entrywise with a contraction in
`N′`. The complete commutator is therefore bounded by twice the matrix
error. The commutant distance formula gives distance at most
that error to `M′`; normalization costs a further factor two for unit balls.
No linear map selecting the matrix approximants is assumed.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixNearCommutantOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance matrixNearCommutantStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
local instance matrixNearCommutantSourceOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance matrixNearCommutantSourceStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

namespace MatrixNearInclusion

variable {M N : VonNeumannAlgebra H} {γ : ℝ}

/-- Individual approximants scale with the norm of the input matrix. -/
theorem scaled_square (h : MatrixNearInclusion M N γ)
    (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M) :
    ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖X - Y‖ ≤ γ * ‖X‖ := by
  by_cases hz : ‖X‖ = 0
  · refine ⟨0, (fun _ _ => N.zero_mem), ?_⟩
    simp only [sub_zero, hz, mul_zero, le_refl]
  have hp : 0 < ‖X‖ := lt_of_le_of_ne (norm_nonneg X) (Ne.symm hz)
  let c : ℂ := ((‖X‖⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = ‖X‖⁻¹ := by
    simp [c]
  obtain ⟨Y, hY, _, hclose⟩ := h n (c • X)
    (fun i j => M.smul_mem (hX i j) c)
    (by rw [norm_smul, hc, inv_mul_cancel₀ hz])
  refine ⟨(‖X‖ : ℂ) • Y, (fun i j => N.smul_mem (hY i j) _), ?_⟩
  have he : X - (‖X‖ : ℂ) • Y = (‖X‖ : ℂ) • (c • X - Y) := by
    rw [smul_sub, smul_smul]
    have hsc : (‖X‖ : ℂ) * c = 1 := by
      simp only [c, ← Complex.ofReal_mul, mul_inv_cancel₀ hz, Complex.ofReal_one]
    rw [hsc, one_smul]
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.le]
  nlinarith

private theorem mapped_derivation_eq
    (a : H →L[ℂ] H) (n : ℕ)
    (X : CStarMatrix (Fin n) (Fin n) (Algebra M)) :
    CStarMatrix.mapₗ ((innerDerivation a).comp M.toStarSubalgebra.subtype.toLinearMap) X =
      diagonalAmplification a * CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toLinearMap X -
        CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toLinearMap X * diagonalAmplification a := by
  apply CStarMatrix.ext
  intro i j
  change a * (X i j).val - (X i j).val * a =
    (Matrix.diagonal (fun _ : Fin n => a) *
      CStarMatrix.ofMatrix.symm (CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toLinearMap X)) i j -
    (CStarMatrix.ofMatrix.symm (CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toLinearMap X) *
      Matrix.diagonal (fun _ : Fin n => a)) i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rfl

/-- Matrix proximity bounds the full derivation of a neighboring
commutant contraction, uniformly at every rectangular matrix level. -/
theorem commutant_complete_bound (h : MatrixNearInclusion M N γ)
    (hγ : 0 ≤ γ) (a : H →L[ℂ] H) (ha : a ∈ N.commutant) (han : ‖a‖ ≤ 1) :
    CompletelyBoundedBy
      ((innerDerivation a).comp M.toStarSubalgebra.subtype.toLinearMap) (2 * γ) := by
  apply completelyBoundedBy_of_large_square
  intro n _ X
  let X₀ := CStarMatrix.mapₗ M.toStarSubalgebra.subtype.toLinearMap X
  obtain ⟨Y, hY, hclose⟩ := h.scaled_square n X₀ (fun i j => (X i j).property)
  have hnX : ‖X₀‖ = ‖X‖ := injective_starAlgHom_matrix_norm
    M.toStarSubalgebra.subtype Subtype.val_injective X
  have hc : diagonalAmplification a * Y = Y * diagonalAmplification a :=
    (diagonalAmplification_commute a Y (fun i j =>
      (VonNeumannAlgebra.mem_commutant_iff.mp ha (Y i j) (hY i j)).symm)).eq
  have hdiag : ‖diagonalAmplification (n := Fin n) a‖ ≤ 1 :=
    (norm_diagonalAmplification_le a).trans han
  rw [mapped_derivation_eq]
  change ‖diagonalAmplification a * X₀ - X₀ * diagonalAmplification a‖ ≤ _
  have he : diagonalAmplification a * X₀ - X₀ * diagonalAmplification a =
      diagonalAmplification a * (X₀ - Y) - (X₀ - Y) * diagonalAmplification a := by
    rw [mul_sub, sub_mul, hc]
    abel
  rw [he]
  calc
    _ ≤ ‖diagonalAmplification (n := Fin n) a * (X₀ - Y)‖ +
        ‖(X₀ - Y) * diagonalAmplification (n := Fin n) a‖ := norm_sub_le _ _
    _ ≤ ‖diagonalAmplification (n := Fin n) a‖ * ‖X₀ - Y‖ +
        ‖X₀ - Y‖ * ‖diagonalAmplification (n := Fin n) a‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 1 * (γ * ‖X₀‖) + (γ * ‖X₀‖) * 1 := by gcongr
    _ = (2 * γ) * ‖X‖ := by rw [hnX]; ring

/-- The factor one-half in the complete commutator distance formula
cancels the factor two in the preceding estimate. -/
theorem commutant_infDist_le (h : MatrixNearInclusion M N γ)
    (hγ : 0 ≤ γ)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall N.commutant) :
    Metric.infDist a (M.commutant : Set (H →L[ℂ] H)) ≤ γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨b, hb, hab⟩ := exists_commutant_approximation_of_complete_bound M hPublished a
    (mul_nonneg (by norm_num) hγ) (h.commutant_complete_bound hγ a ha.1 ha.2)
    (γ + ε) (by linarith)
  exact (Metric.infDist_le_dist_of_mem hb).trans
    (by simpa only [dist_eq_norm] using hab.le)

/-- The algebra near-inclusion is contravariant and needs no normalization
loss. The larger constant is needed only for proximity of unit balls. -/
theorem commutant_nearInclusion (h : MatrixNearInclusion M N γ)
    (hγ : 0 ≤ γ)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    {η : ℝ} (hγη : γ < η) : NearInclusion N.commutant M.commutant η :=
  ⟨γ, hγη, h.commutant_infDist_le hγ hPublished⟩

/-- Normalization yields a commutant unit-ball approximant with any error
strictly larger than twice the matrix gap. -/
theorem exists_commutant_unitBall_approx (h : MatrixNearInclusion M N γ)
    (hγ : 0 ≤ γ)
    (hPublished : PublishedBlockCommutantApproximation (Algebra M) H)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall N.commutant)
    {η : ℝ} (hγη : 2 * γ < η) :
    ∃ b ∈ unitBall M.commutant, ‖a - b‖ < η := by
  obtain ⟨b, hb, hab⟩ := exists_commutant_approximation_of_complete_bound M hPublished a
    (mul_nonneg (by norm_num) hγ) (h.commutant_complete_bound hγ a ha.1 ha.2)
    (η / 2) (by linarith)
  obtain ⟨c, hc, hac⟩ := exists_unitBall_approx_of_algebra_approx ha.2 hb
  exact ⟨c, hc, hac.trans_lt (by linarith)⟩

/-- Two-sided matrix proximity controls the ordinary commutant gap. -/
theorem commutant_kkDistance_le (hMN : MatrixNearInclusion M N γ)
    (hNM : MatrixNearInclusion N M γ) (hγ : 0 ≤ γ)
    (hM : PublishedBlockCommutantApproximation (Algebra M) H)
    (hN : PublishedBlockCommutantApproximation (Algebra N) H) :
    kkDistance M.commutant N.commutant ≤ 2 * γ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hbound := kkDistance_le_two_mul_of_nearInclusions (M := M.commutant)
    (N := N.commutant) (γ := γ + ε / 2) (by linarith)
    (hNM.commutant_nearInclusion hγ hN (by linarith))
    (hMN.commutant_nearInclusion hγ hM (by linarith))
  linarith

end MatrixNearInclusion

end

end KadisonKastler

end OAI
