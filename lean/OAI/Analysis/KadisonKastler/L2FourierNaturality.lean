import OAI.Analysis.KadisonKastler.L2TensorCoordinates
import OAI.Analysis.KadisonKastler.RegularFourierTransport

namespace OAI

/-! # Fourier transport through the cyclic spectral coordinates -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform TensorProduct

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
private theorem postcomp_toLp (L : H →L[ℂ] K) (f : SchwartzMap ℝ H) :
    (SchwartzMap.postcompCLM L f).toLp 2 = L.compLp (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(SchwartzMap.postcompCLM L f).coeFn_toLp 2,
    f.coeFn_toLp 2, L.coeFn_compLp (f.toLp 2)] with t h₁ h₂ h₃
  rw [h₁, h₃, h₂]
  rfl

private theorem fourier_postcomp (L : H →L[ℂ] K) (f : SchwartzMap ℝ H) (t : ℝ) :
    (𝓕 (SchwartzMap.postcompCLM L f)) t = L ((𝓕 f) t) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  simp only [Real.fourier_eq, SchwartzMap.postcompCLM_apply]
  rw [← L.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  apply integral_congr_ae
  filter_upwards [] with s
  simp only [Circle.smul_def, map_smul]

theorem fourier_compLp (L : H →L[ℂ] K) (f : Lp H 2 (volume : Measure ℝ)) :
    (𝓕 (L.compLp f) : Lp K 2 (volume : Measure ℝ)) = L.compLp (𝓕 f) := by
  let A : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) :=
    (Lp.fourierTransformₗᵢ ℝ K).toContinuousLinearEquiv.toContinuousLinearMap.comp (L.compLpL 2 volume)
  let B : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) :=
    (L.compLpL 2 volume).comp (Lp.fourierTransformₗᵢ ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  have he : A = B := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer A.continuous B.continuous
    funext g
    change (𝓕 (L.compLp (g.toLp 2)) : Lp K 2 (volume : Measure ℝ)) = L.compLp (𝓕 (g.toLp 2))
    rw [← postcomp_toLp, SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq]
    apply Lp.ext
    filter_upwards [(𝓕 (SchwartzMap.postcompCLM L g)).coeFn_toLp 2,
      (𝓕 g).coeFn_toLp 2, L.coeFn_compLp ((𝓕 g).toLp 2)] with t h₁ h₂ h₃
    rw [h₁, h₃, h₂]
    exact fourier_postcomp L g t
  exact congrArg (fun T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp K 2 (volume : Measure ℝ) => T f) he

theorem fourier_scalarLpTensor (f : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    (𝓕 (scalarLpTensor volume f x) : Lp H 2 (volume : Measure ℝ)) =
      scalarLpTensor volume (𝓕 f) x :=
  fourier_compLp (ContinuousLinearMap.toSpanSingleton ℂ x) f

omit [CompleteSpace H] [CompleteSpace K] in
theorem compLp_scalarLpTensor {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (L : H →L[ℂ] K) (f : Lp ℂ 2 μ) (x : H) :
    L.compLp (scalarLpTensor μ f x) = scalarLpTensor μ f (L x) := by
  apply Lp.ext
  filter_upwards [L.coeFn_compLp (scalarLpTensor μ f x), scalarLpTensor_apply_ae μ f x,
    scalarLpTensor_apply_ae μ f (L x)] with s hL hx hy
  rw [hL, hx, hy, map_smul]

theorem l2ScalarSwap_fourier {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : Lp (Lp ℂ 2 μ) 2 (volume : Measure ℝ)) :
    l2ScalarSwap volume μ (𝓕 F) =
      (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
        (l2ScalarSwap volume μ F) := by
  let L := (Lp.fourierTransformₗᵢ ℝ ℂ).toContinuousLinearEquiv.toContinuousLinearMap
  refine (l2TensorEmbedding_dense volume).induction_on
    (p := fun F => l2ScalarSwap volume μ (𝓕 F) = L.compLp (l2ScalarSwap volume μ F)) F ?_ ?_
  · exact isClosed_eq ((l2ScalarSwap volume μ).continuous.comp
      (Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ)).continuous)
      ((L.compLpL 2 μ).continuous.comp (l2ScalarSwap volume μ).continuous)
  · intro z
    induction z using TensorProduct.inductionOn with
    | tmul f x =>
        change l2ScalarSwap volume μ (𝓕 (scalarLpTensor volume f x)) =
          L.compLp (l2ScalarSwap volume μ (scalarLpTensor volume f x))
        rw [fourier_scalarLpTensor, l2ScalarSwap_tensor, l2ScalarSwap_tensor,
          compLp_scalarLpTensor]
        rfl
    | add z w hz hw =>
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume z)) = _ at hz
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume w)) = _ at hw
        have hadd (a b : Lp (Lp ℂ 2 (volume : Measure ℝ)) 2 μ) :
            L.compLp (a + b) = L.compLp a + L.compLp b := (L.compLpL 2 μ).map_add a b
        change l2ScalarSwap volume μ ((Lp.fourierTransformₗᵢ ℝ (Lp ℂ 2 μ))
          (l2TensorEmbedding volume (z + w))) = _
        simpa only [map_add, hadd] using congrArg₂ (· + ·) hz hw

end

end KadisonKastler

end OAI
