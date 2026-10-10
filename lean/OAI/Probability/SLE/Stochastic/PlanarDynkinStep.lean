import OAI.Probability.SLE.Stochastic.PlanarWienerAverage
import OAI.Probability.SLE.Stochastic.PlanarGaussianRegularity
import OAI.Probability.SLE.Stochastic.PlanarDriftError
import OAI.Probability.SLE.Stochastic.PlanarGeneratorRegularity

namespace OAI

/-! Uniform one-step error for compact smooth planar Brownian tests. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

lemma planarWiener_taylor_set_error
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ≥0, ∀ (s δ : ℝ≥0) (A : Set (Driver×Driver)),
      MeasurableSet[planarWienerFiltration s] A →
      |(∫ b in A, f (planarWiener (s+δ) b)-f (planarWiener s b) ∂W.prod W)-
        (δ:ℝ)*(∫ b in A, planarGenerator f (planarWiener s b) ∂W.prod W)| ≤
        (C:ℝ)*(δ:ℝ)*Real.sqrt δ := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C,hC⟩ := compact_planar_gaussian_generator f hf hc
  obtain ⟨K,hK,_⟩ := compact_smooth_bounded_lipschitz f hf hc
  obtain ⟨D,hD,_⟩ := planarGenerator_bounded_lipschitz f hf hc
  have hKb (z) : |f z|≤K := by simpa only [Real.norm_eq_abs] using hK z
  refine ⟨C,?_⟩
  intro s δ A hA
  have hI (t) : Integrable (fun b => f (planarWiener t b)) ((W.prod W).restrict A) :=
    Integrable.of_bound (hf.continuous.measurable.comp (measurable_planarWiener t)).aestronglyMeasurable K
      (Eventually.of_forall fun b => hK _)
  have hGI : Integrable (fun b => planarGenerator f (planarWiener s b)) ((W.prod W).restrict A) :=
    Integrable.of_bound ((planarGenerator_smooth f hf).continuous.measurable.comp
      (measurable_planarWiener s)).aestronglyMeasurable D
        (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hD _)
  have hMI : Integrable (fun b => planarGaussianMean δ f (planarWiener s b).1 (planarWiener s b).2)
      ((W.prod W).restrict A) :=
    Integrable.of_bound ((planarGaussianMean_measurable δ f hf.continuous K hKb).comp
      (measurable_planarWiener s)).aestronglyMeasurable K
        (Eventually.of_forall fun b => by
          simpa only [Real.norm_eq_abs] using
            (planarGaussianMean_bound δ f hf.continuous K hKb (planarWiener s b)))
  let R (b : Driver×Driver) := planarGaussianMean δ f (planarWiener s b).1 (planarWiener s b).2-
    f (planarWiener s b)-(δ:ℝ)*planarGenerator f (planarWiener s b)
  have he : (∫ b in A, f (planarWiener (s+δ) b)-f (planarWiener s b) ∂W.prod W)-
      (δ:ℝ)*(∫ b in A, planarGenerator f (planarWiener s b) ∂W.prod W) =
      ∫ b in A, R b ∂W.prod W := by
    rw [integral_sub (hI _) (hI _),planarWiener_set_integral_average W hW s δ A hA f hf.continuous K hKb]
    dsimp only [R]
    have hSI : Integrable (fun b => planarGaussianMean δ f (planarWiener s b).1 (planarWiener s b).2-
        f (planarWiener s b)) ((W.prod W).restrict A) := hMI.sub (hI s)
    have hDI : Integrable (fun b => (δ:ℝ)*planarGenerator f (planarWiener s b))
        ((W.prod W).restrict A) := hGI.const_mul _
    rw [integral_sub hSI hDI,integral_sub hMI (hI s),integral_const_mul]
  rw [he]
  have hb := norm_integral_le_of_norm_le_const (μ := (W.prod W).restrict A)
    (f := R) (C := (C:ℝ)*(δ:ℝ)*Real.sqrt δ)
    (Eventually.of_forall fun b => by simpa only [Real.norm_eq_abs] using hC δ (planarWiener s b))
  calc
    _ ≤ (C:ℝ)*(δ:ℝ)*Real.sqrt δ*((W.prod W).restrict A).real univ := by
      simpa only [Real.norm_eq_abs] using hb
    _ ≤ (C:ℝ)*(δ:ℝ)*Real.sqrt δ := by
      have hm : ((W.prod W).restrict A).real univ ≤ 1 := by
        simpa only [measureReal_def,Measure.restrict_apply_univ] using
          (measureReal_le_one (μ := W.prod W) (s := A))
      exact mul_le_of_le_one_right (by positivity) hm

lemma planarWiener_one_step_error
    (W : WienerLaw) (hW : IsWiener W) (f : ℝ×ℝ → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ≥0, ∀ (s δ : ℝ≥0) (A : Set (Driver×Driver)),
      MeasurableSet[planarWienerFiltration s] A →
      |(∫ b in A, f (planarWiener (s+δ) b)-f (planarWiener s b) ∂W.prod W)-
        (∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), planarGenerator f (planarWiener u.toNNReal b)) ∂W.prod W)| ≤
        (C:ℝ)*(δ:ℝ)*Real.sqrt δ := by
  obtain ⟨C,hC⟩ := planarWiener_taylor_set_error W hW f hf hc
  obtain ⟨L,hL,hLip⟩ := planarGenerator_bounded_lipschitz f hf hc
  let M : ℝ≥0 := ⟨standardGaussianAbsMoment 1,standardGaussianAbsMoment_nonneg 1⟩
  refine ⟨C+2*L*M,?_⟩
  intro s δ A hA
  have he := planarWiener_integrated_drift_error W hW s δ A (planarGenerator f) L L hL hLip
  calc
    _ ≤ |(∫ b in A, f (planarWiener (s+δ) b)-f (planarWiener s b) ∂W.prod W)-
          (δ:ℝ)*(∫ b in A, planarGenerator f (planarWiener s b) ∂W.prod W)|+
        |(δ:ℝ)*(∫ b in A, planarGenerator f (planarWiener s b) ∂W.prod W)-
          (∫ b in A, (∫ u in (s:ℝ)..(s+δ:ℝ≥0), planarGenerator f (planarWiener u.toNNReal b)) ∂W.prod W)| :=
      abs_sub_le _ _ _
    _ ≤ (C:ℝ)*(δ:ℝ)*Real.sqrt δ+(L:ℝ)*2*(δ:ℝ)*Real.sqrt δ*standardGaussianAbsMoment 1 :=
      add_le_add (hC s δ A hA) he
    _ = _ := by
      change _ = ((C:ℝ)+2*(L:ℝ)*standardGaussianAbsMoment 1)*(δ:ℝ)*Real.sqrt δ
      ring

end SLEExactGauge

end

end OAI
