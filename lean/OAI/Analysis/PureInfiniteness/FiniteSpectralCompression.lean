import OAI.Analysis.PureInfiniteness.SpectralRowSampling
import OAI.Analysis.PureInfiniteness.FiniteCompressionError

namespace OAI

/-! Quantitative commutation of the actual finite spectral compression. The
proof uses its first and second moments and a diagonal compressed coefficient. -/

noncomputable section

namespace WeakPureInfiniteness

variable {A J : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype J] [DecidableEq J]

omit [PartialOrder A] [StarOrderedRing A] [DecidableEq J] in
lemma rowColumn_conjugation (H : CStarMatrix (Fin 1) J A)
    (G : CStarMatrix J (Fin 1) A) (b : CStarMatrix (Fin 1) (Fin 1) A) :
    (H * G).conjTranspose * b * (H * G) =
      columnReturn G (H.conjTranspose * b * H) := by
  simp only [columnReturn, rectangular_conjTranspose_mul, rectangular_mul_assoc]

omit [DecidableEq J] in
lemma row_sandwich_norm_le (H : CStarMatrix (Fin 1) J A) (hH : ‖H‖ ≤ 1)
    (b : CStarMatrix (Fin 1) (Fin 1) A) : ‖H.conjTranspose * b * H‖ ≤ ‖b‖ := by
  calc
    _ ≤ ‖H.conjTranspose * b‖ * ‖H‖ := rectangular_norm_mul_le _ _
    _ ≤ (‖H.conjTranspose‖ * ‖b‖) * ‖H‖ :=
      mul_le_mul_of_nonneg_right (rectangular_norm_mul_le _ _) (norm_nonneg _)
    _ = (‖H‖ * ‖b‖) * ‖H‖ := by rw [rectangular_norm_conjTranspose]
    _ ≤ (1 * ‖b‖) * 1 := by gcongr
    _ = _ := by ring

lemma finite_spectral_compression_commutator
    (H : CStarMatrix (Fin 1) J A) (hH : ‖H‖ ≤ 1)
    (g : J → A) (hg : ∀ j, 0 ≤ g j) (hgsum : ‖∑ j, g j‖ ≤ 1)
    (t : J → ℝ) (a b : CStarMatrix (Fin 1) (Fin 1) A)
    (hb : b.conjTranspose = b)
    (hoff : ∀ i j, i ≠ j → (H.conjTranspose * b * H) i j = 0)
    (ε q : ℝ)
    (hfirst : ‖columnReturn (sqrtColumn g) (scalarSample t) - a‖ ≤ ε)
    (hsecond : ‖columnReturn (sqrtColumn g) (scalarSample t * scalarSample t) - a * a‖ ≤ q) :
    let d := H * sqrtColumn g
    ‖a * (d.conjTranspose * b * d) - (d.conjTranspose * b * d) * a‖ ≤
      (2 * ε + 2 * Real.sqrt (q + ε * (2 * ‖a‖ + ε))) * ‖b‖ := by
  let G := sqrtColumn g
  let S : CStarMatrix J J A := scalarSample t
  let Y := H.conjTranspose * b * H
  have hG : ‖G‖ ≤ 1 := sqrtColumn_norm_le_one g hg hgsum
  have hS : S.conjTranspose = S := scalarSample_selfAdjoint t
  have hY : Y.conjTranspose = Y := by
    simp only [Y, rectangular_conjTranspose_mul, rectangular_conjTranspose_conjTranspose,
      hb, rectangular_mul_assoc]
  have hSY : S * Y = Y * S := by
    rw [diagonal_of_offdiagonal_zero Y hoff]
    exact scalarSample_commute_diagonal t _
  have hε : 0 ≤ ε := (norm_nonneg _).trans hfirst
  have hD := columnReturn_schwarz_defect_le_of_moments G S a ε q hfirst hsecond
  have hYn : ‖Y‖ ≤ ‖b‖ := row_sandwich_norm_le H hH b
  have he := columnReturn_approximate_commutator_le G hG S Y hS hY hSY a ε
    (by simpa only [norm_sub_rev] using hfirst)
  dsimp only
  rw [rowColumn_conjugation]
  calc
    _ ≤ 2 * ε * ‖Y‖ +
        2 * Real.sqrt ‖columnReturn G (S * S) - columnReturn G S * columnReturn G S‖ * ‖Y‖ := he
    _ ≤ 2 * ε * ‖b‖ + 2 * Real.sqrt (q + ε * (2 * ‖a‖ + ε)) * ‖b‖ := by
      gcongr
    _ = _ := by ring

end WeakPureInfiniteness

end

end OAI
