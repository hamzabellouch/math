import Mathlib
import OAI.Probability.SKGap.Brownian.BrownianPathFernique

namespace OAI

section

noncomputable section
namespace SKGap.PathBridge
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology

def pathEnergy (n : ℕ) (f : Fin n→UnitPath) : ℝ := ∑ i,‖f i‖^2

lemma energy_exponential_prod (n : ℕ) (a : ℝ) (f : Fin n→UnitPath) :
    exp (a*pathEnergy n f)=∏ i,exp (a*‖f i‖^2) := by
  rw [pathEnergy,Finset.mul_sum,exp_sum]

lemma pathEnergy_exponential_integrable (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (a : ℝ) (hi : Integrable (fun f : UnitPath=>exp (a*‖f‖^2)) μ) (n : ℕ) :
    Integrable (fun f=>exp (a*pathEnergy n f)) (Measure.pi (fun _ : Fin n=>μ)) := by
  simp_rw [energy_exponential_prod]
  exact Integrable.fintype_prod (fun _=>hi)

lemma pathEnergy_exponential_integral (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (a : ℝ) (n : ℕ) :
    (∫ f,exp (a*pathEnergy n f) ∂Measure.pi (fun _ : Fin n=>μ))=
      (∫ f : UnitPath,exp (a*‖f‖^2) ∂μ)^n := by
  simp_rw [energy_exponential_prod]
  simpa using integral_fintype_prod_eq_pow (ι:=Fin n) (μ:=μ) (fun f : UnitPath=>exp (a*‖f‖^2))

theorem pathEnergy_dimension_tail (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) :
    ∃ H : ℝ, 0<H ∧ ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>μ)).real {f | H*(n:ℝ) ≤ pathEnergy n f} ≤ exp (-(n:ℝ)) := by
  obtain ⟨a,ha,hi⟩ := centered_gaussian_path_fernique μ hG h0
  let M := ∫ f : UnitPath,exp (a*‖f‖^2) ∂μ
  have hM : 1≤M := by
    calc
      1 = ∫ _ : UnitPath,(1:ℝ) ∂μ := by simp
      _ ≤ M := integral_mono (integrable_const _) hi (fun f=>by
        exact one_le_exp_iff.mpr (mul_nonneg ha.le (sq_nonneg _)))
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  let H := (log M+1)/a
  have hH : 0<H := div_pos (by linarith [log_nonneg hM]) ha
  refine ⟨H,hH,fun n=>?_⟩
  calc
    _ ≤ exp (-a*(H*(n:ℝ)))*mgf (pathEnergy n) (Measure.pi (fun _ : Fin n=>μ)) a :=
      measure_ge_le_exp_mul_mgf _ ha.le (pathEnergy_exponential_integrable μ a hi n)
    _ = exp (-(n:ℝ)) := by
      rw [mgf,pathEnergy_exponential_integral]
      change exp (-a*(H*(n:ℝ)))*M^n=_
      rw [← exp_log hMp,← exp_nat_mul,← exp_add]
      congr 1
      dsimp [H]
      field_simp
      ring

theorem scaledPath_dimension_tail (μ : Measure UnitPath) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : UnitInterval=>fun f : UnitPath=>f t) μ)
    (h0 : ∀ t : UnitInterval, ∫ f : UnitPath,f t ∂μ=0) {κ : ℝ} (hκ : 0<κ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>μ)).real
        {f | κ^2*(n:ℝ) ≤ δ*pathEnergy n f} ≤ exp (-(n:ℝ)) := by
  obtain ⟨H,hH,ht⟩ := pathEnergy_dimension_tail μ hG h0
  refine ⟨κ^2/H,div_pos (sq_pos_of_pos hκ) hH,fun n=>?_⟩
  convert ht n using 2
  ext f
  simp only [Set.mem_ofPred_eq]
  rw [div_mul_eq_mul_div,le_div_iff₀ hH]
  constructor <;> intro h
  · nlinarith [sq_pos_of_pos hκ]
  · nlinarith [sq_pos_of_pos hκ]
end SKGap.PathBridge

end
end

section

noncomputable section
namespace SKGap.PathBridge
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

def brownianUnitLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0→Ω→ℝ) : Measure UnitPath :=
  P.map (continuousPathVersion (unitBrownianProcess B))

lemma brownianUnitLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0→Ω→ℝ} (hB : IsBrownianReal B P) :
    IsProbabilityMeasure (brownianUnitLaw P B) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact inferInstanceAs (IsProbabilityMeasure (P.map _))

theorem brownianUnitLaw_eq {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {B : ℝ≥0→Ω→ℝ} {C : ℝ≥0→Ω'→ℝ}
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C Q) :
    brownianUnitLaw P B=brownianUnitLaw Q C := by
  classical
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let : IsProbabilityMeasure Q := hC.isGaussianProcess.isProbabilityMeasure
  have hmB := aemeasurable_continuousPathVersion (brownian_unit_gaussian hB).aemeasurable
    (brownian_unit_continuous hB)
  have hmC := aemeasurable_continuousPathVersion (brownian_unit_gaussian hC).aemeasurable
    (brownian_unit_continuous hC)
  apply measurableEmbedding_pathEvaluations.map_injective
  unfold brownianUnitLaw
  rw [AEMeasurable.map_map_of_aemeasurable measurableEmbedding_pathEvaluations.measurable.aemeasurable hmB,
    AEMeasurable.map_map_of_aemeasurable measurableEmbedding_pathEvaluations.measurable.aemeasurable hmC]
  have hpB := isProjectiveLimit_map
    (measurableEmbedding_pathEvaluations.measurable.comp_aemeasurable hmB)
  have hpC := isProjectiveLimit_map
    (measurableEmbedding_pathEvaluations.measurable.comp_aemeasurable hmC)
  suffices heq : ∀ s : Finset ℕ,
      P.map (fun ω=>s.restrict (pathEvaluations (continuousPathVersion (unitBrownianProcess B) ω)))=
      Q.map (fun ω=>s.restrict (pathEvaluations (continuousPathVersion (unitBrownianProcess C) ω))) by
    simp only [Function.comp_apply] at hpB hpC
    simp_rw [heq] at hpB
    exact hpB.unique hpC
  intro s
  let d : ℕ→ℝ≥0 := fun k=>⟨(denseSeq UnitInterval k).1,(denseSeq UnitInterval k).2.1⟩
  let I := s.image d
  let e : (I→ℝ)→s→ℝ := fun v i=>v ⟨d i,Finset.mem_image.mpr ⟨i,i.2,rfl⟩⟩
  have he : Measurable e := by fun_prop
  have hb := congrArg (Measure.map e) (hB.hasLaw I).map_eq
  have hc := congrArg (Measure.map e) (hC.hasLaw I).map_eq
  rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable (hB.hasLaw I).aemeasurable] at hb
  rw [AEMeasurable.map_map_of_aemeasurable he.aemeasurable (hC.hasLaw I).aemeasurable] at hc
  calc
    _ = P.map (e ∘ (fun ω=>I.restrict (B · ω))) := by
      apply Measure.map_congr
      have hall : ∀ᵐ ω ∂P, ∀ k : s,
          continuousPathVersion (unitBrownianProcess B) ω (denseSeq UnitInterval k) =
            unitBrownianProcess B (denseSeq UnitInterval k) ω :=
        ae_all_iff.mpr (fun k=>continuousPathVersion_eval (brownian_unit_continuous hB) _)
      filter_upwards [hall] with ω hω
      ext k
      change continuousPathVersion (unitBrownianProcess B) ω (denseSeq UnitInterval k) = B (d k) ω
      exact hω k
    _ = Q.map (e ∘ (fun ω=>I.restrict (C · ω))) := hb.trans hc.symm
    _ = _ := by
      apply Measure.map_congr
      have hall : ∀ᵐ ω ∂Q, ∀ k : s,
          continuousPathVersion (unitBrownianProcess C) ω (denseSeq UnitInterval k) =
            unitBrownianProcess C (denseSeq UnitInterval k) ω :=
        ae_all_iff.mpr (fun k=>continuousPathVersion_eval (brownian_unit_continuous hC) _)
      filter_upwards [hall] with ω hω
      ext k
      change C (d k) ω = continuousPathVersion (unitBrownianProcess C) ω (denseSeq UnitInterval k)
      exact (hω k).symm

theorem brownian_normalized_increment_tail {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0→Ω→ℝ} (hB : IsBrownianReal B P) :
    ∃ H : ℝ, 0<H ∧ ∀ s δ : ℝ≥0, δ≠0 → ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n=>brownianUnitLaw P
        (fun t ω=>(sqrt δ)⁻¹*(B (s+δ*t) ω-B s ω)))).real
        {f | H*(n:ℝ) ≤ pathEnergy n f} ≤ exp (-(n:ℝ)) := by
  let := brownianUnitLaw_probability hB
  obtain ⟨H,hH,hTail⟩ := pathEnergy_dimension_tail (brownianUnitLaw P B)
    (gaussian_continuousPathVersion (brownian_unit_gaussian hB) (brownian_unit_continuous hB))
    (fun t=>by
      rw [brownianUnitLaw,mean_continuousPathVersion (brownian_unit_gaussian hB).aemeasurable
        (brownian_unit_continuous hB)]
      exact hB.integral_eval _)
  refine ⟨H,hH,fun s δ hδ n=>?_⟩
  have hb := (hB.shift s).smul hδ
  have he := brownianUnitLaw_eq hb hB
  simpa only [he] using hTail n
end SKGap.PathBridge

end
end

end OAI
