import Mathlib
import OAI.Probability.SKRatio.Matrices.PathEvaluations
import OAI.Probability.SKRatio.Matrices.PathEnergy

namespace OAI

section
section
noncomputable section
namespace SKRatioGaussian.PathBridge
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology

def brownianUnitLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0→Ω→ℝ) : Measure UnitPath :=
  P.map (continuousPathVersion (unitBrownianProcess B))

lemma brownianUnitLaw_probability {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0→Ω→ℝ} (hB : IsBrownianReal B P) :
    IsProbabilityMeasure (brownianUnitLaw P B) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact (Measure.isProbabilityMeasure_map_iff
    (aemeasurable_continuousPathVersion (brownian_unit_gaussian hB).aemeasurable
      (brownian_unit_continuous hB))).2 inferInstance

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
end SKRatioGaussian.PathBridge

end
end

section

noncomputable section

end
end
end

end OAI
