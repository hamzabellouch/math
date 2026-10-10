import OAI.Probability.PosteriorReplicas.Measures.DensityTools

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace PosteriorReplicas

def transposeCLE (m k : ℕ) : (Fin m → Fin k → ℝ) ≃L[ℝ] (Fin k → Fin m → ℝ) :=
  ({ toFun := fun z j i => z i j
     invFun := fun z i j => z j i
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } :
        (Fin m → Fin k → ℝ) ≃ₗ[ℝ] (Fin k → Fin m → ℝ)).toContinuousLinearEquiv

@[simp] lemma transposeCLE_apply (m k : ℕ) (z : Fin m → Fin k → ℝ) :
    transposeCLE m k z = fun j i => z i j := rfl

lemma matrix_volume_unit_cube (m k : ℕ) :
    (volume : Measure (Fin m → Fin k → ℝ)) (Icc 0 1) = 1 := by
  rw [← pi_univ_Icc, volume_pi_pi]
  simp only [Pi.zero_apply, Pi.one_apply, Real.volume_Icc_pi, sub_zero,
    ENNReal.ofReal_one, Finset.prod_const_one]

instance matrixPiVolumeAddHaar (m k : ℕ) :
    (volume : Measure (Fin m → Fin k → ℝ)).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure (fun _ : Fin m => (volume : Measure (Fin k → ℝ)))

lemma transpose_volume_preserving (m k : ℕ) :
    MeasurePreserving (transposeCLE m k) volume volume := by
  let e := transposeCLE m k
  have h := Measure.isAddLeftInvariant_eq_smul ((volume : Measure (Fin m → Fin k → ℝ)).map e)
    (volume : Measure (Fin k → Fin m → ℝ))
  have he : e ⁻¹' Icc 0 1 = Icc 0 1 := by
    ext z
    simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply,
      e, transposeCLE_apply]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> exact ⟨fun i j => h₁ j i, fun i j => h₂ j i⟩
  have hc := congrArg (fun μ : Measure (Fin k → Fin m → ℝ) => μ (Icc 0 1)) h
  rw [Measure.map_apply e.continuous.measurable measurableSet_Icc, he,
    matrix_volume_unit_cube, Measure.smul_apply, matrix_volume_unit_cube,
    ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  refine ⟨e.continuous.measurable, ?_⟩
  rw [h]
  have hc' : ((volume : Measure (Fin m → Fin k → ℝ)).map e).addHaarScalarFactor volume = 1 :=
    ENNReal.coe_inj.mp (by simpa only [ENNReal.coe_one] using hc.symm)
  rw [hc', one_smul]

def matrixNormal (m k : ℕ) : Measure (Fin m → Fin k → ℝ) :=
  Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1

instance (m k : ℕ) : IsProbabilityMeasure (matrixNormal m k) := by
  unfold matrixNormal
  infer_instance

def noiseScale (n : ℕ) : ℝ := 1 / (n + 1)

lemma noiseScale_pos (n : ℕ) : 0 < noiseScale n := by unfold noiseScale; positivity
lemma tendsto_noiseScale : Filter.Tendsto noiseScale Filter.atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def matrixNoiseDensity (m k n : ℕ) (z : Fin m → Fin k → ℝ) : ℝ≥0∞ :=
  ∏ i, ∏ j, gaussianPDF 0 (⟨(noiseScale n)^2, sq_nonneg _⟩ : ℝ≥0) (z i j)

@[fun_prop] lemma measurable_matrixNoiseDensity (m k n : ℕ) :
    Measurable (matrixNoiseDensity m k n) := by
  unfold matrixNoiseDensity
  fun_prop

lemma matrixNormal_scale (m k n : ℕ) :
    (matrixNormal m k).map (fun z => noiseScale n • z) =
      volume.withDensity (matrixNoiseDensity m k n) := by
  let v : ℝ≥0 := ⟨(noiseScale n)^2, sq_nonneg _⟩
  have hv : v ≠ 0 := by
    intro h
    have hh : (noiseScale n)^2 = 0 := congrArg NNReal.toReal h
    exact (sq_pos_of_pos (noiseScale_pos n)).ne' hh
  have hg : (gaussianReal 0 1).map (fun x => noiseScale n * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := 0) (v := 1) (noiseScale n)
    rw [mul_zero, mul_one] at h
    exact h
  have hgd : gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v) :=
    gaussianReal_of_var_ne_zero _ hv
  have : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 v)) := hgd ▸ inferInstance
  have hlabel : (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map
      (fun z => noiseScale n • z) =
        (volume : Measure (Fin k → ℝ)).withDensity (fun z => ∏ j, gaussianPDF 0 v (z j)) := by
    change (Measure.pi (fun _ : Fin k => gaussianReal 0 1)).map
      (fun z i => noiseScale n * z i) = _
    rw [Measure.pi_map_pi (fun _ => (show Measurable (fun x : ℝ => noiseScale n * x) by fun_prop).aemeasurable)]
    simp_rw [hg, hgd]
    exact pi_withDensity _ _ (fun _ => measurable_gaussianPDF _ _)
  have : IsProbabilityMeasure ((volume : Measure (Fin k → ℝ)).withDensity
      (fun z => ∏ j, gaussianPDF 0 v (z j))) := by
    rw [← hlabel]
    infer_instance
  change (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin k => gaussianReal 0 1))).map
    (fun z i => noiseScale n • z i) = _
  rw [Measure.pi_map_pi (fun _ => (show Measurable (fun z : Fin k → ℝ => noiseScale n • z) by fun_prop).aemeasurable)]
  simp_rw [hlabel]
  exact pi_withDensity _ _ (fun _ => by fun_prop)

lemma matrix_noise_shrinks {m k : ℕ} (z : Fin m → Fin k → ℝ) :
    Filter.Tendsto (fun n => noiseScale n • z) Filter.atTop (nhds 0) := by
  simpa using tendsto_noiseScale.smul_const z

end PosteriorReplicas

namespace PosteriorReplicas
lemma matrixNoise_convolution {m k n : ℕ} (c : Fin m → Fin k → ℝ)
    {F : (Fin m → Fin k → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, matrixNoiseDensity m k n (y-c) * F y ∂volume =
      ∫⁻ z, F (c + noiseScale n • z) ∂matrixNormal m k := by
  have hf : Measurable (fun y => matrixNoiseDensity m k n (y-c) * F y) := by fun_prop
  rw [← (measurePreserving_add_left (volume : Measure (Fin m → Fin k → ℝ)) c).lintegral_comp hf]
  simp only [add_sub_cancel_left]
  have he := lintegral_withDensity_eq_lintegral_mul (volume : Measure (Fin m → Fin k → ℝ))
    (measurable_matrixNoiseDensity m k n)
    (show Measurable (fun y => F (c+y)) from hF.comp (by fun_prop))
  simp only [Pi.mul_apply] at he
  rw [← he, ← matrixNormal_scale m k n,
    lintegral_map (show Measurable (fun y => F (c+y)) by fun_prop) (by fun_prop)]

lemma matrixNoise_transpose_lintegral {m k n : ℕ}
    {F : (Fin k → Fin m → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y, matrixNoiseDensity m k n (transposeCLE k m y) * F y ∂volume =
      ∫⁻ z, F (transposeCLE m k (noiseScale n • z)) ∂matrixNormal m k := by
  have hf : Measurable (fun y => matrixNoiseDensity m k n (transposeCLE k m y) * F y) := by fun_prop
  rw [← (transpose_volume_preserving m k).lintegral_comp hf]
  simp only [transposeCLE_apply]
  have he := lintegral_withDensity_eq_lintegral_mul (volume : Measure (Fin m → Fin k → ℝ))
    (measurable_matrixNoiseDensity m k n)
    (show Measurable (fun y : Fin m → Fin k → ℝ => F (fun j i => y i j)) from hF.comp (by fun_prop))
  simp only [Pi.mul_apply] at he
  rw [← he, ← matrixNormal_scale m k n,
    lintegral_map (show Measurable (fun y : Fin m → Fin k → ℝ => F (fun j i => y i j)) by fun_prop) (by fun_prop)]
end PosteriorReplicas
end

end OAI
