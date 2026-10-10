import OAI.Analysis.CircleDomains.Probability.FullLevelNullImage
import OAI.Analysis.CircleDomains.Sobolev.CoareaZeroProduct
import OAI.Analysis.CircleDomains.Sobolev.ComplexGradientError
import OAI.Analysis.CircleDomains.Sobolev.BorelSobolevGradient
import OAI.Analysis.CircleDomains.Sobolev.SummableSobolevApproximation

namespace OAI

/-! Null scalar images of almost every full height level, constructed
from the actual smooth approximation and the scalar coarea identity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem sobolev_coordinate_level_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0 ∨ W.weakGrad p = 0) :
    ∀ᵐ t ∂volume, volume ((U ∘ complexPlaneCoordinates.symm) '' (F ∩ {z | v z = t})) = 0 := by
  let K := complexPlaneCoordinates ⁻¹' Q
  have hK : IsCompact K := complexPlaneCoordinates.toHomeomorph.isCompact_preimage.mpr hQ
  let B := borelSobolevWitness W
  let G : Fin 2 → Lp ℝ 2 (volume : Measure EuclideanPlane) := scalarGradientRepresentative W
  obtain ⟨φ, hφ, hφU, hφG⟩ := exists_summable_sobolev_approximation isOpen_univ hK
    (subset_univ _) B hU
  let f : Fin 2 → ℕ → EuclideanPlane → ℝ := fun i n p =>
    fderiv ℝ (φ n) p (EuclideanSpace.single i 1)-G i p
  have hf (i : Fin 2) (n : ℕ) : Measurable (f i n) :=
    (((hφ n).1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.sub
      (Lp.stronglyMeasurable (G i)).measurable
  have hfL (i : Fin 2) (n : ℕ) : MemLp (f i n) 2 (volume.restrict K) := by
    have hD : MemLp (fun p => fderiv ℝ (φ n) p (EuclideanSpace.single i 1)) 2 volume := (((hφ n).1.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hφ n).2.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    exact (hD.restrict K).sub ((Lp.memLp (G i)).restrict K)
  have hfs (i : Fin 2) : Summable (fun n => (eLpNorm (f i n) 2 (volume.restrict K)).toReal) :=
    hφG i
  let q : EuclideanPlane → ℝ := fun p => |G 0 p|+|G 1 p|
  have hq : Measurable q := (Lp.stronglyMeasurable (G 0)).measurable.abs.add
    (Lp.stronglyMeasurable (G 1)).measurable.abs
  have hq0 (p : EuclideanPlane) : 0 ≤ q p := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hqL : MemLp q 2 (volume.restrict K) :=
    (((Lp.memLp (G 0)).norm.add (Lp.memLp (G 1)).norm).restrict K)
  let g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (q (complexPlaneCoordinates.symm z))
  let e : ℕ → ℂ → ℝ≥0∞ := fun n z =>
    ENNReal.ofReal ‖f 0 n (complexPlaneCoordinates.symm z)‖+
      ENNReal.ofReal ‖f 1 n (complexPlaneCoordinates.symm z)‖
  have hg : Measurable g := ENNReal.measurable_ofReal.comp
    (hq.comp complexPlaneCoordinates.symm.continuous.measurable)
  have hgf : ∀ᵐ t ∂volume,
      (∫⁻ z in Q ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) < ∞ := by
    have ht := complex_coarea_L2_weight_finite hcoarea hv hw hLp hQ hq hqL
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hq0 _)] using ht
  have hgz : ∀ᵐ t ∂volume,
      (∫⁻ z in F ∩ {z | v z = t}, g z ∂(μH[1] : Measure ℂ)) = 0 :=
    complex_coarea_zero_product hcoarea hv hw hLp hF (ENNReal.measurable_ofReal.comp hq) (by
      have h0 := (scalarGradientRepresentative_ae W 0).filter_mono
        (ae_mono (Measure.restrict_le_self (s := complexPlaneCoordinates ⁻¹' F)))
      have h1 := (scalarGradientRepresentative_ae W 1).filter_mono
        (ae_mono (Measure.restrict_le_self (s := complexPlaneCoordinates ⁻¹' F)))
      filter_upwards [hz, h0, h1] with p hp hp0 hp1
      rcases hp with hp | hp
      · simp only [hp, norm_zero, ENNReal.ofReal_zero, mul_zero]
      · have hG0 : G 0 p = 0 := by simpa only [hp, PiLp.zero_apply] using hp0
        have hG1 : G 1 p = 0 := by simpa only [hp, PiLp.zero_apply] using hp1
        simp [q, hG0, hG1])
  have he (i : Fin 2) := complex_coarea_L2_errors hcoarea hv hw hLp hQ
    (f i) (hf i) (hfL i) (hfs i)
  have he0 : ∀ᵐ t ∂volume, Tendsto (fun n =>
      ∫⁻ z in Q ∩ {z | v z = t}, e n z ∂(μH[1] : Measure ℂ)) atTop (𝓝 0) := by
    filter_upwards [he 0, he 1] with t ht0 ht1
    have ht := ht0.add ht1
    simp only [add_zero] at ht
    convert ht using 1
    funext n
    exact lintegral_add_left
      (ENNReal.measurable_ofReal.comp ((hf 0 n).norm.comp
        complexPlaneCoordinates.symm.continuous.measurable)) _
  apply full_level_null_image_of_approximation ψ hv hlim hQ hF.measurableSet hFQ
    (fun n => φ n ∘ complexPlaneCoordinates.symm)
    (fun n => ((hφ n).1.comp complexPlaneCoordinates.symm.contDiff).of_le (by simp))
    (fun z hzQ => hφU.tendsto_at hzQ) g hg e ?_
    (complex_coarea_finite_levels hcoarea hv hw hLp hQ) hgf hgz he0
  intro n z
  have hp := complex_scalar_gradient_error (hφ n).1 (complexPlaneCoordinates.symm z)
    (G 0 (complexPlaneCoordinates.symm z)) (G 1 (complexPlaneCoordinates.symm z))
  rw [complexPlaneCoordinates.apply_symm_apply] at hp
  have hh := ENNReal.ofReal_le_ofReal hp
  change ENNReal.ofReal ‖fderiv ℝ (φ n ∘ complexPlaneCoordinates.symm) z‖ ≤
    ENNReal.ofReal (q (complexPlaneCoordinates.symm z) +
      (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|)) at hh
  have hsplit : ENNReal.ofReal (q (complexPlaneCoordinates.symm z) +
      (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|)) =
      g z+e n z := by
    calc
      _ = ENNReal.ofReal (q (complexPlaneCoordinates.symm z)) +
          ENNReal.ofReal (|f 0 n (complexPlaneCoordinates.symm z)|+|f 1 n (complexPlaneCoordinates.symm z)|) :=
        ENNReal.ofReal_add (hq0 _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by
        dsimp only [g, e]
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        congr 1
        exact ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
  exact hh.trans_eq hsplit


 theorem sobolev_height_level_null_image
    (hcoarea : PlanarSobolevCoarea)
    (ψ : ℕ → ℂ ≃ₜ ℂ) {v : ℂ → ℝ} (hv : Continuous v)
    (hlim : TendstoLocallyUniformly (fun n z => (ψ n z).im) v atTop)
    {V : EuclideanPlane → EuclideanPlane}
    (hw : DeGiorgi.HasWeakGrad V (v ∘ complexPlaneCoordinates) univ)
    (hLp : ∀ R i, MemLp (fun p => V p i) 2 (volume.restrict (ball 0 R)))
    {F Q : Set ℂ} (hF : IsCompact F) (hQ : IsCompact Q) (hFQ : F ⊆ interior Q)
    (hz : ∀ᵐ p ∂volume.restrict (complexPlaneCoordinates ⁻¹' F), V p = 0)
    {U : EuclideanPlane → ℝ} (hU : Continuous U)
    (W : DeGiorgi.MemW1pWitness 2 U univ) :
    ∀ᵐ t ∂volume, volume ((U ∘ complexPlaneCoordinates.symm) '' (F ∩ {z | v z = t})) = 0 :=
  sobolev_coordinate_level_null_image hcoarea ψ hv hlim hw hLp hF hQ hFQ hU W
    (hz.mono (fun _ hp => Or.inl hp))

end CircleDomainRigidity

end

end OAI
