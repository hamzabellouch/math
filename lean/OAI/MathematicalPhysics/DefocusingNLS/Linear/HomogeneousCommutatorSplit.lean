import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFrequencySplit

namespace OAI

/-! # Exact low/high decomposition of the physical commutator -/

open MeasureTheory LineDeriv Filter Topology
open scoped SchwartzMap LineDeriv

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousOrderedCommutator_add (N : ℕ) (j : Fin N → Fin 12)
    (V f g : 𝓢(E, ℂ)) :
    homogeneousOrderedCommutator N j V (f + g) =
      homogeneousOrderedCommutator N j V f + homogeneousOrderedCommutator N j V g := by
  simp only [homogeneousOrderedCommutator, homogeneousOrderedDerivative, map_add,
    iteratedLineDerivOp_add]
  abel

theorem homogeneousOrderedCommutator_split (N : ℕ) (j : Fin N → Fin 12)
    (V f : 𝓢(E, ℂ)) (R : ℝ) (hR : 0 < R) :
    homogeneousOrderedCommutator N j V f =
      homogeneousOrderedCommutator N j V (homogeneousLowFrequencyPart R hR f) +
        homogeneousOrderedCommutator N j V (homogeneousHighFrequencyPart R hR f) := by
  rw [← homogeneousOrderedCommutator_add]
  congr 1
  dsimp only [homogeneousHighFrequencyPart]
  abel

theorem homogeneousLowCommutator_fourier_row (a k R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 0 < R)
    (N : ℕ) (j : Fin N → Fin 12) (V f : 𝓢(E, ℂ)) (ξ : E) :
    radianFourierKernel
      (homogeneousOrderedCommutator N j V (homogeneousLowFrequencyPart R hR f)) ξ =
      ((((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) : ℂ) *
        homogeneousCommutatorRow a k ha ha1 hk N j V (homogeneousFrequencyCutoff R hR) ξ
          (homogeneousSchwartzEmbedding a k ha ha1 hk f) := by
  rw [homogeneousOrderedCommutator_fourier]
  change _ = _ * homogeneousCommutatorRow a k ha ha1 hk N j V
    (homogeneousFrequencyCutoff R hR) ξ
    (homogeneousFrequencyEmbedding a k ha ha1 hk (radianFourierKernel f))
  rw [homogeneousCommutatorRow_Schwartz]
  congr 1
  rw [← integral_sub_left_eq_self
    (fun η : E => (homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j (ξ - η)) *
      radianFourierKernel V η * radianFourierKernel (homogeneousLowFrequencyPart R hR f) (ξ - η))
    volume ξ]
  apply integral_congr_ae
  filter_upwards [] with η
  simp only [sub_sub_self, homogeneousLowFrequencyPart_fourier, homogeneousCommutatorRowKernel]
  ring

theorem tendsto_homogeneousLowCommutator_fourier_L2 (a k M R : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hR : 1 ≤ R)
    (N : ℕ) (j : Fin N → Fin 12) (V : 𝓢(E, ℂ)) (f : ℕ → 𝓢(E, ℂ))
    (hf : ∀ n, ‖homogeneousSchwartzEmbedding a k ha ha1 hk (f n)‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousSchwartzEmbedding a k ha ha1 hk (f n))) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ : E, ‖radianFourierKernel
      (homogeneousOrderedCommutator N j V
        (homogeneousLowFrequencyPart R (by linarith) (f n))) ξ‖ ^ 2) atTop (𝓝 0) := by
  have ht := tendsto_homogeneousCommutator_cutoff_L2 a k M (2 * R) ha ha1 hk
    (by linarith) N j V (homogeneousFrequencyCutoff R (by linarith))
    (fun η hη => homogeneousFrequencyCutoff_zero R (by linarith) η hη.le)
    (fun n => homogeneousSchwartzEmbedding a k ha ha1 hk (f n)) hf hweak
  have he (n : ℕ) :
      (∫ ξ : E, ‖radianFourierKernel
        (homogeneousOrderedCommutator N j V
          (homogeneousLowFrequencyPart R (by linarith) (f n))) ξ‖ ^ 2) =
      (((2 * Real.pi) ^ (12 : ℕ))⁻¹) ^ 2 *
        ∫ ξ : E, ‖homogeneousCommutatorRow a k ha ha1 hk N j V
          (homogeneousFrequencyCutoff R (by linarith)) ξ
          (homogeneousSchwartzEmbedding a k ha ha1 hk (f n))‖ ^ 2 := by
    simp_rw [homogeneousLowCommutator_fourier_row a k R ha ha1 hk (by linarith),
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show 0 < ((2 * Real.pi) ^ (12 : ℕ))⁻¹ by positivity), mul_pow]
    rw [integral_const_mul]
  simp_rw [he]
  simpa only [mul_zero] using ht.const_mul ((((2 * Real.pi) ^ (12 : ℕ))⁻¹) ^ 2)

end DefocusingNLS

end OAI
