import OAI.Probability.PosteriorReplicas.Learners.CompletedKernelLaw

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal RealInnerProductSpace unitInterval
noncomputable section
namespace PosteriorRegression

namespace CompletedKernelLearner
open Learner

def uniformSuccess {d M : ℕ} (K : CompletedKernelLearner d M) (T : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ z : UnitSphere d × Samples d T,
    K.estimateLaw z.1 z.2 {ŝ | angularError z.1 ŝ ≤ ε}
    ∂((uniformSphere d).prod (sampleLaw d T))

lemma angularBall_measurable {d : ℕ} (s : UnitSphere d) (ε : ℝ) :
    MeasurableSet {ŝ : UnitSphere d | angularError s ŝ ≤ ε} := by
  exact measurableSet_le (Real.continuous_arccos.measurable.comp
    (measurable_subtype_coe.inner measurable_const)) measurable_const

lemma Realization.uniformSuccess_eq {d M T : ℕ} (hd : 3≤d) {K : CompletedKernelLearner d M}
    (R : Realization K) (ε : ℝ) :
    (R.toLearner T).uniformSuccess (coinsLaw T) ε = K.uniformSuccess T ε := by
  have : NeZero d := ⟨by omega⟩
  let S : Set (UnitSphere d × (Coins T × Samples d T)) :=
    {z | angularError z.1 ((R.toLearner T).estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T))) :=
    (R.uniformAdmissible hd).angularSuccess_nullMeasurable ε
  let e : ((UnitSphere d × Samples d T) × Coins T) ≃ᵐ
      UnitSphere d × (Coins T × Samples d T) :=
    MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm)
  have he : MeasurePreserving e
      (((uniformSphere d).prod (sampleLaw d T)).prod (coinsLaw T))
      ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T))) :=
    ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := coinsLaw T))).comp
      (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) (coinsLaw T))
  have hQ := hS.preimage he.quasiMeasurePreserving
  have hI := (aemeasurable_const : AEMeasurable (fun _ : (UnitSphere d × Samples d T) × Coins T => (1 : ℝ≥0∞))
      (((uniformSphere d).prod (sampleLaw d T)).prod (coinsLaw T))).indicator₀ hQ
  change ((uniformSphere d).prod ((coinsLaw T).prod (sampleLaw d T))) S = _
  rw [← he.measure_preimage hS]
  rw [← one_mul ((((uniformSphere d).prod (sampleLaw d T)).prod (coinsLaw T)) (e ⁻¹' S)),
    ← lintegral_indicator_const₀ hQ 1, lintegral_prod _ hI]
  unfold uniformSuccess
  apply lintegral_congr
  intro z
  have hball := angularBall_measurable z.1 ε
  rw [← R.estimate_law z.1 z.2, Measure.map_apply (R.measurable_estimate z.1 z.2) hball]
  have hm : MeasurableSet {ω : Coins T | angularError z.1 ((R.toLearner T).estimate z.1 ω z.2) ≤ ε} :=
    (R.measurable_estimate z.1 z.2) hball
  change (∫⁻ ω, ({ω : Coins T | angularError z.1 ((R.toLearner T).estimate z.1 ω z.2) ≤ ε}).indicator
    (fun _ => (1 : ℝ≥0∞)) ω ∂coinsLaw T) = _
  rw [lintegral_indicator_const hm]
  simp only [one_mul]
  rfl

lemma uniformSuccess_le_one {d M : ℕ} [NeZero d] (K : CompletedKernelLearner d M) (T : ℕ) (ε : ℝ) :
    K.uniformSuccess T ε ≤ 1 := by
  apply (lintegral_mono (fun z => prob_le_one)).trans
  simp

lemma fixed_quadratic_memory {d M T : ℕ} {A : ℝ} (hA : 0<A) (hd : 32≤d)
    (hM : (M : ℝ)≤A*(d : ℝ)^2) {ε : ℝ} (hε : 0<ε) (hε10 : ε≤1/10)
    (K : CompletedKernelLearner d M) (hs : (2/3 : ℝ≥0∞) ≤ K.uniformSuccess T ε) :
    (1/(4*(400000+100*A))) * (d : ℝ) * Real.log (1/ε) ≤ (T : ℝ) := by
  have he := K.realization.uniformSuccess_eq (T := T) (by omega) ε
  exact source_fixed_quadratic_memory hA hd hM hε hε10 (coinsLaw T)
    (K.realization.toLearner T) (K.realization.uniformAdmissible (by omega)) (by simpa only [he] using hs)

end CompletedKernelLearner
end PosteriorRegression
end

end OAI
