import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousCommutatorFourier

namespace OAI

/-! # Bounded rows of the frequency-localized commutator

Each row of the actual commutator kernel, after a fixed Schwartz frequency
cutoff, is a bounded functional on the faithful homogeneous space. This
gives pointwise convergence from weak convergence without assuming an
unproved compact operator.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousCommutatorRowKernel (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (ξ η : E) : ℂ :=
  (homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j η) *
    radianFourierKernel V (ξ - η) * χ η

noncomputable def homogeneousCommutatorRowBound (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (ξ : E) : ℝ :=
  (‖homogeneousOrderedSymbol N j ξ‖ * SchwartzMap.seminorm ℝ 0 0 χ +
    SchwartzMap.seminorm ℝ N 0 χ) * SchwartzMap.seminorm ℝ 0 0 (radianFourierKernel V)

theorem homogeneousCommutatorRowKernel_continuous (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (ξ : E) : Continuous (homogeneousCommutatorRowKernel N j V χ ξ) := by
  unfold homogeneousCommutatorRowKernel homogeneousOrderedSymbol
  fun_prop

theorem homogeneousCommutatorRowBound_nonneg (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (ξ : E) : 0 ≤ homogeneousCommutatorRowBound N j V χ ξ := by
  unfold homogeneousCommutatorRowBound
  positivity

theorem homogeneousCommutatorRowKernel_norm_le (N : ℕ) (j : Fin N → Fin 12)
    (V χ : 𝓢(E, ℂ)) (ξ η : E) :
    ‖homogeneousCommutatorRowKernel N j V χ ξ η‖ ≤
      homogeneousCommutatorRowBound N j V χ ξ := by
  have hχ := SchwartzMap.norm_le_seminorm ℝ χ η
  have hd : ‖homogeneousOrderedSymbol N j η‖ * ‖χ η‖ ≤
      SchwartzMap.seminorm ℝ N 0 χ :=
    (mul_le_mul_of_nonneg_right (homogeneousOrderedSymbol_norm_le N j η) (norm_nonneg _)).trans
      (SchwartzMap.norm_pow_mul_le_seminorm ℝ χ N η)
  have hV := SchwartzMap.norm_le_seminorm ℝ (radianFourierKernel V) (ξ - η)
  calc
    _ = ‖homogeneousOrderedSymbol N j ξ - homogeneousOrderedSymbol N j η‖ *
        ‖χ η‖ * ‖radianFourierKernel V (ξ - η)‖ := by
      simp only [homogeneousCommutatorRowKernel, norm_mul]
      ring
    _ ≤ (‖homogeneousOrderedSymbol N j ξ‖ * ‖χ η‖ +
        ‖homogeneousOrderedSymbol N j η‖ * ‖χ η‖) *
        ‖radianFourierKernel V (ξ - η)‖ := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (norm_nonneg _)) (norm_nonneg _)
    _ ≤ _ := mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left hχ (norm_nonneg _)) hd)
      hV (norm_nonneg _) (by positivity)

theorem homogeneousCommutatorRow_integrable (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E) (u : HomogeneousY a k) :
    Integrable (fun η : E => homogeneousCommutatorRowKernel N j V χ ξ η * u η) := by
  apply (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)).1.bdd_mul
    (c := homogeneousCommutatorRowBound N j V χ ξ)
    (homogeneousCommutatorRowKernel_continuous N j V χ ξ).aestronglyMeasurable
  exact ae_of_all _ (homogeneousCommutatorRowKernel_norm_le N j V χ ξ)

noncomputable def homogeneousCommutatorRowValue (a k : ℝ)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E) (u : HomogeneousY a k) : ℂ :=
  ∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η * u η

theorem homogeneousCommutatorRowValue_norm_le (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E) (u : HomogeneousY a k) :
    ‖homogeneousCommutatorRowValue a k N j V χ ξ u‖ ≤
      (homogeneousCommutatorRowBound N j V χ ξ *
        Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹)) * ‖u‖ := by
  let C := homogeneousCommutatorRowBound N j V χ ξ
  have hC : 0 ≤ C := homogeneousCommutatorRowBound_nonneg N j V χ ξ
  have hu := integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp u)
  have hn : Real.sqrt (∫ η : E, ‖u η‖ ^ 2 ∂homogeneousFourierMeasure a k) = ‖u‖ := by
    rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num
  have hlu : (∫ η : E, ‖u η‖) ≤
      Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹) * ‖u‖ := by
    simpa only [hn] using hu.2
  have hm := integral_mono_of_nonneg (ae_of_all _ (fun η : E => norm_nonneg
    (homogeneousCommutatorRowKernel N j V χ ξ η * u η)))
    (hu.1.norm.const_mul C) (ae_of_all _ (fun η => by
      change ‖homogeneousCommutatorRowKernel N j V χ ξ η * u η‖ ≤ C * ‖u η‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (homogeneousCommutatorRowKernel_norm_le N j V χ ξ η)
        (norm_nonneg _)))
  calc
    _ ≤ ∫ η : E, ‖homogeneousCommutatorRowKernel N j V χ ξ η * u η‖ :=
      norm_integral_le_integral_norm _
    _ ≤ C * ∫ η : E, ‖u η‖ := hm.trans_eq (integral_const_mul _ _)
    _ ≤ C * (Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹) * ‖u‖) :=
      mul_le_mul_of_nonneg_left hlu hC
    _ = _ := by ring

noncomputable def homogeneousCommutatorRow (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E) :
    HomogeneousY a k →L[ℂ] ℂ := by
  let A : HomogeneousY a k →ₗ[ℂ] ℂ :=
    { toFun := homogeneousCommutatorRowValue a k N j V χ ξ
      map_add' := by
        intro u v
        have huv := (Lp.coeFn_add u v).filter_mono
          (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
        change (∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η * (u + v) η) = _
        rw [integral_congr_ae (by
          filter_upwards [huv] with η hη
          rw [hη, Pi.add_apply, mul_add]),
          integral_add (homogeneousCommutatorRow_integrable a k ha ha1 hk N j V χ ξ u)
            (homogeneousCommutatorRow_integrable a k ha ha1 hk N j V χ ξ v)]
        rfl
      map_smul' := by
        intro c u
        have hcu := (Lp.coeFn_smul c u).filter_mono
          (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
        change (∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η * (c • u) η) =
          c * ∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η * u η
        have he : (fun η : E => homogeneousCommutatorRowKernel N j V χ ξ η * (c • u) η) =ᵐ[volume]
            (fun η : E => c * (homogeneousCommutatorRowKernel N j V χ ξ η * u η)) := by
          filter_upwards [hcu] with η hη
          simp only [hη, Pi.smul_apply, smul_eq_mul]
          ring
        rw [integral_congr_ae he, integral_const_mul] }
  exact A.mkContinuous (homogeneousCommutatorRowBound N j V χ ξ *
    Real.sqrt (∫ η : E, (homogeneousFourierWeight a k η)⁻¹))
    (homogeneousCommutatorRowValue_norm_le a k ha ha1 hk N j V χ ξ)

theorem homogeneousCommutatorRow_Schwartz (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ ψ : 𝓢(E, ℂ)) (ξ : E) :
    homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ
      (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) =
      ∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η * ψ η := by
  let := homogeneousFourierMeasure_temperate a k ha ha1 hk
  have hψ := (SchwartzMap.coeFn_toLp ψ 2 (homogeneousFourierMeasure a k)).filter_mono
    (volume_absolutelyContinuous_homogeneousFourierMeasure a k ha1 hk).ae_le
  change (∫ η : E, homogeneousCommutatorRowKernel N j V χ ξ η *
    (homogeneousFrequencyEmbedding a k ha ha1 hk ψ) η) = _
  apply integral_congr_ae
  filter_upwards [hψ] with η hη
  change _ * ψ.toLp 2 (homogeneousFourierMeasure a k) η = _
  rw [hη]

theorem tendsto_homogeneousCommutatorRow_of_weakNull (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (N : ℕ) (j : Fin N → Fin 12) (V χ : 𝓢(E, ℂ)) (ξ : E)
    (u : ℕ → HomogeneousY a k)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 0)) :
    Tendsto (fun n => homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ (u n))
      atTop (𝓝 0) :=
  hweak ((homogeneousCommutatorRow a k ha ha1 hk N j V χ ξ).restrictScalars ℝ)

end DefocusingNLS

end OAI
