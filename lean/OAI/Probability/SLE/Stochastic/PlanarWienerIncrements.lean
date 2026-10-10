import OAI.Probability.SLE.Stochastic.IndependentPlanarIncrements

namespace OAI

/-! The two-coordinate Wiener increment has its exact product Gaussian
law and is independent of both coordinate pasts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open Target

def planarWiener (t : ℝ≥0) (b : Driver×Driver) : ℝ×ℝ := (b.1 t,b.2 t)

def planarWienerPast (s : ℝ≥0) (b : Driver×Driver) :
    (Iic s → ℝ)×(Iic s → ℝ) := (fun t => b.1 t,fun t => b.2 t)

lemma measurable_planarWiener (t : ℝ≥0) : Measurable (planarWiener t) := by
  exact ((continuous_eval_const t).measurable.comp measurable_fst).prodMk
    ((continuous_eval_const t).measurable.comp measurable_snd)

lemma measurable_planarWienerPast (s : ℝ≥0) : Measurable (planarWienerPast s) := by
  apply Measurable.prodMk
  · exact measurable_pi_iff.mpr (fun t => (continuous_eval_const (t:ℝ≥0)).measurable.comp measurable_fst)
  · exact measurable_pi_iff.mpr (fun t => (continuous_eval_const (t:ℝ≥0)).measurable.comp measurable_snd)

lemma planarWiener_increment_law (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) :
    HasLaw (fun b => planarWiener (s+δ) b-planarWiener s b)
      ((gaussianReal 0 δ).prod (gaussianReal 0 δ)) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun b : Driver => b (s+δ)-b s) :=
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable
  have hL : HasLaw (fun b : Driver => b (s+δ)-b s) (gaussianReal 0 δ) W :=
    (hW.shift s).hasLaw_eval δ
  have h1 : HasLaw (fun b : Driver×Driver => b.1 (s+δ)-b.1 s)
      (gaussianReal 0 δ) (W.prod W) := hL.comp measurePreserving_fst.hasLaw
  have h2 : HasLaw (fun b : Driver×Driver => b.2 (s+δ)-b.2 s)
      (gaussianReal 0 δ) (W.prod W) := hL.comp measurePreserving_snd.hasLaw
  exact (indepFun_prod hm hm).hasLaw_prod h1 h2

lemma planarWiener_increment_indep_past (W : WienerLaw) (hW : IsWiener W) (s δ : ℝ≥0) :
    IndepFun (planarWienerPast s)
      (fun b => planarWiener (s+δ) b-planarWiener s b) (W.prod W) := by
  let : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  have hp : Measurable (fun b : Driver => fun t : Iic s => b t) :=
    measurable_pi_iff.mpr (fun t => (continuous_eval_const (t:ℝ≥0)).measurable)
  have hi : Measurable (fun b : Driver => b (s+δ)-b s) :=
    (continuous_eval_const _).measurable.sub (continuous_eval_const _).measurable
  have hind : IndepFun (fun b : Driver => fun t : Iic s => b t)
      (fun b : Driver => b (s+δ)-b s) W := by
    exact ((hW.indepFun_shift s).comp (measurable_pi_apply δ) measurable_id).symm
  exact independent_product_pairs hp hi hp hi hind hind

end SLEExactGauge

end

end OAI
