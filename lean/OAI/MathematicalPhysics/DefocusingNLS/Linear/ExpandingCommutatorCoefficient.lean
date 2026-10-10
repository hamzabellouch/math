import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProductCommutatorLinear

namespace OAI

/-! # Uniform continuity in the product commutator coefficient -/

open scoped ENNReal

namespace DefocusingNLS

theorem expandingOrderedFourierEnergy_norm_le (a L : ℝ) (N : ℕ) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (f : FourierL2) :
    ‖expandingOrderedFourierEnergy a L N hL j f‖ ≤ ‖f‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro n
  rw [expandingOrderedFourierEnergy_apply, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (expandingOrderedMultiplier_norm_le a L N hL j n)

theorem expandingProductCommutator_norm_le (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f : FourierL2) :
    ‖expandingProductCommutator a L N ha ha1 hN hL j q f‖ ≤
      ((2 * Real.sqrt (4 ^ (N : ℝ)) + 1) * expandingEmbeddingBound a N) * ‖q‖ * ‖f‖ := by
  have hc := fourierConvolution_norm_le (expandingFourierCoefficient a N L q)
    (summable_norm_expandingFourierCoefficient a N L ha ha1 hN hL q)
    (expandingOrderedFourierEnergy a L N hL j f)
  have hc' : ‖fourierConvolution (expandingFourierCoefficient a N L q)
      (expandingOrderedFourierEnergy a L N hL j f)‖ ≤
        (expandingEmbeddingBound a N * ‖q‖) * ‖f‖ :=
    hc.trans (mul_le_mul (tsum_norm_expandingFourierCoefficient_le a N L ha ha1 hN hL q)
      (expandingOrderedFourierEnergy_norm_le a L N hL j f) (norm_nonneg _)
      (by unfold expandingEmbeddingBound; positivity))
  have hp := (expandingOrderedFourierEnergy_norm_le a L N hL j
    (expandingProduct a N L ha ha1 hN hL q f)).trans
      (expandingProduct_norm_le a N L ha ha1 hN hL q f)
  exact (norm_sub_le _ _).trans ((add_le_add hp hc').trans_eq (by ring))

theorem fourierConvolution_sub_left (v w : frequencyLattice → ℂ)
    (hv : Summable (fun n => ‖v n‖)) (hw : Summable (fun n => ‖w n‖)) (f : FourierL2) :
    fourierConvolution (v - w) f = fourierConvolution v f - fourierConvolution w f := by
  unfold fourierConvolution
  simp only [Pi.sub_apply, sub_smul]
  exact (summable_fourierConvolution_terms v hv f).tsum_sub
    (summable_fourierConvolution_terms w hw f)

theorem expandingProductCommutator_sub_left (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q r f : FourierL2) :
    expandingProductCommutator a L N ha ha1 hN hL j (q - r) f =
      expandingProductCommutator a L N ha ha1 hN hL j q f -
        expandingProductCommutator a L N ha ha1 hN hL j r f := by
  have hp : expandingProduct a N L ha ha1 hN hL (q - r) f =
      expandingProduct a N L ha ha1 hN hL q f - expandingProduct a N L ha ha1 hN hL r f := by
    exact congrArg (fun B : FourierL2 →L[ℂ] FourierL2 => B f)
      ((expandingBilinearProduct a N L ha ha1 hN hL).map_sub q r)
  have hv : expandingFourierCoefficient a N L (q - r) =
      expandingFourierCoefficient a N L q - expandingFourierCoefficient a N L r := by
    funext n
    simp only [expandingFourierCoefficient, lp.coeFn_sub, Pi.sub_apply, mul_sub]
  unfold expandingProductCommutator
  rw [hp, map_sub, hv, fourierConvolution_sub_left _ _
    (summable_norm_expandingFourierCoefficient a N L ha ha1 hN hL q)
    (summable_norm_expandingFourierCoefficient a N L ha ha1 hN hL r)]
  abel

theorem expandingProductCommutator_coefficient_difference (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q r f : FourierL2) :
    ‖expandingProductCommutator a L N ha ha1 hN hL j q f -
      expandingProductCommutator a L N ha ha1 hN hL j r f‖ ≤
        ((2 * Real.sqrt (4 ^ (N : ℝ)) + 1) * expandingEmbeddingBound a N) * ‖q - r‖ * ‖f‖ := by
  rw [← expandingProductCommutator_sub_left]
  exact expandingProductCommutator_norm_le a L N ha ha1 hN hL j (q - r) f

end DefocusingNLS

end OAI
