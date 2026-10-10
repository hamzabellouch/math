import Mathlib
import OAI.Probability.Perceptron.Variational.GibbsRestoration
import OAI.Probability.Perceptron.Sphere.UnitSphereTangent
import OAI.Probability.Perceptron.Pressure.TerminalRestorationCoefficients
import OAI.Probability.Perceptron.Variational.LeafMarginalLaw

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

section
section
variable {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]

lemma gibbsReplicaMean_pair_integral (μ : Measure S) [IsProbabilityMeasure μ]
    {H : S→ℝ} (hH : Measurable H) (hi : Integrable (fun x => Real.exp (H x)) μ)
    (F : S×S→ℝ) (hF : Measurable F) :
    gibbsReplicaMean μ H 2 (fun x => F (x 0,x 1)) =
      ∫ x, F x ∂(tiltLaw μ H 1).prod (tiltLaw μ H 1) := by
  have hi' : Integrable (fun x => Real.exp (1*H x)) μ := by simpa only [one_mul] using hi
  let := tilt_law_probability_of_integrable μ hi'
  rw [gibbsReplicaMean_integral_of_integrable μ hH hi]
  have hp := measurePreserving_finTwoArrow (tiltLaw μ H 1)
  have he := integral_map (μ:=Measure.pi fun _ : Fin 2 => tiltLaw μ H 1)
    hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

lemma gibbsReplicaMean_product_leaf (μ : Measure S) (ν : Measure T)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (H : S×T→ℝ) (G : T→ℝ) (hH : Measurable H) (hG : Measurable G)
    (hi : Integrable (fun x => Real.exp (H x)) (μ.prod ν))
    (hp : ∀ t, (∫ s, Real.exp (H (s,t)) ∂μ)=Real.exp (G t))
    (r : ℕ) (F : (Fin r→T)→ℝ) (hF : Measurable F) :
    gibbsReplicaMean (μ.prod ν) H r (fun x => F (fun i => (x i).2)) =
      gibbsReplicaMean ν G r F := by
  have hiG : Integrable (fun t => Real.exp (G t)) ν := by simpa only [hp] using hi.integral_prod_right
  rw [gibbsReplicaMean_integral_of_integrable (μ.prod ν) hH hi,
    gibbsReplicaMean_integral_of_integrable ν hG hiG]
  have hmap := tiltLaw_prod_snd_replica μ ν H G hH hG hi hp r
  have he := integral_map (μ:=Measure.pi fun _ : Fin r => tiltLaw (μ.prod ν) H 1)
    hmap.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hmap.map_eq] at he
  exact he.symm

end
variable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]

lemma indexedTerminalPairMean_replica (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (d : Fin (n+1)) (f : X→ℝ)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l))) (indexedLeafProbability n p.1)) :
    indexedTerminalPairMean step n H x d f p =
      gibbsReplicaMean (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p) 2
        (fun l => if indexedCommonDepth n (l 0) (l 1)=d then
          f (indexedLeafState step n (x,p.2) (l 0))*f (indexedLeafState step n (x,p.2) (l 1)) else 0) := by
  unfold indexedTerminalPairMean
  dsimp only
  rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _
    (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
  symm
  exact gibbsReplicaMean_pair_integral (indexedLeafProbability n p.1)
    (H:=indexedTerminalEnergy step n H x p) (measurable_of_countable _)
    (by simpa only [indexedTerminalEnergy] using hi)
    (fun l : IndexedLeaf n×IndexedLeaf n => if indexedCommonDepth n l.1 l.2=d then
      f (indexedLeafState step n (x,p.2) l.1)*f (indexedLeafState step n (x,p.2) l.2) else 0)
    (measurable_of_countable _)

lemma indexedTerminalMean_tiltMean (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (H : X→ℝ) (hH : Measurable H) (x : X) (f : X→ℝ)
    (p : IndexedCascadeBase n×IndexedCascadeMarks S n)
    (hi : Integrable (fun l => Real.exp (H (indexedLeafState step n (x,p.2) l))) (indexedLeafProbability n p.1)) :
    indexedTerminalMean step n H x f p =
      tiltMean (indexedLeafProbability n p.1) (indexedTerminalEnergy step n H x p)
        (fun l => f (indexedLeafState step n (x,p.2) l)) 1 := by
  unfold indexedTerminalMean
  rw [gibbsProbabilityKernel_of_integrable (indexedTerminalBaseKernel n) _
    (indexedTerminalEnergy_measurable step hs n H hH x) p hi]
  exact tilt_law_integral_of_integrable (indexedLeafProbability n p.1) (measurable_of_countable _)
    (by simpa only [one_mul,indexedTerminalEnergy] using hi)

lemma indexedTerminalPairMean_restore (step : X×S→X) (hs : Measurable step)
    (n : ℕ) (J W : X→ℝ) (hJ : Measurable J) (hW : Measurable W)
    (x : X) (d : Fin (n+1)) (f : X→ℝ) (p : IndexedCascadeBase n×IndexedCascadeMarks S n)
    (hiJ : Integrable (fun l => Real.exp (J (indexedLeafState step n (x,p.2) l))) (indexedLeafProbability n p.1))
    (hi : Integrable (fun l => Real.exp (J (indexedLeafState step n (x,p.2) l)+W (indexedLeafState step n (x,p.2) l)))
      (indexedLeafProbability n p.1)) :
    indexedTerminalPairMean step n (fun y => J y+W y) x d f p =
      gibbsReplicaMean (indexedLeafProbability n p.1) (indexedTerminalEnergy step n J x p) 2
        (fun l => (∏ i, Real.exp (W (indexedLeafState step n (x,p.2) (l i)))) *
          (if indexedCommonDepth n (l 0) (l 1)=d then
            f (indexedLeafState step n (x,p.2) (l 0))*f (indexedLeafState step n (x,p.2) (l 1)) else 0)) /
        (tiltMean (indexedLeafProbability n p.1) (indexedTerminalEnergy step n J x p)
          (fun l => Real.exp (W (indexedLeafState step n (x,p.2) l))) 1)^2 := by
  have he := indexedTerminalPairMean_replica step hs n (fun y => J y+W y)
    (show Measurable (fun y => J y+W y) from hJ.add hW) x d f p hi
  rw [he]
  change gibbsReplicaMean _ (fun l => J (indexedLeafState step n (x,p.2) l)+W (indexedLeafState step n (x,p.2) l)) 2 _ = _
  exact gibbsReplicaMean_restore (indexedLeafProbability n p.1) (measurable_of_countable _) hiJ 2 _

end

lemma continuous_integrable_compact {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X→ℝ} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma unitSphere_gibbs_tangent_mean (n : ℕ) (y : NormalizedSpin (n+1))
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*(∫ x : NormalizedSpin (n+1), spinOverlap x y*G (spinOverlap x y)
      ∂tiltLaw (unitSphereLaw (n+1)) (fun x => H x.val) 1) =
      ∫ x : NormalizedSpin (n+1),
        deriv G (spinOverlap x y)*(1-spinOverlap x y^2)+G (spinOverlap x y)*
          fderiv ℝ H x.val (y.val-spinOverlap x y • x.val)
        ∂tiltLaw (unitSphereLaw (n+1)) (fun x => H x.val) 1 := by
  have hHc : Continuous (fun x : NormalizedSpin (n+1) => H x.val) := hH.continuous.comp continuous_subtype_val
  have hi := continuous_integrable_compact (μ:=unitSphereLaw (n+1)) (Real.continuous_exp.comp hHc)
  have hi' : Integrable (fun x : NormalizedSpin (n+1) => Real.exp (1*H x.val)) (unitSphereLaw (n+1)) := by
    simpa only [one_mul,Function.comp_def] using hi
  rw [tilt_law_integral_of_integrable _ hHc.measurable hi',
    tilt_law_integral_of_integrable _ hHc.measurable hi']
  have he := unitSphere_gibbs_tangent_integral n y hH hG
  have hr (x : NormalizedSpin (n+1)) : spinOverlap y x=spinOverlap x y := real_inner_comm _ _
  simp_rw [hr] at he
  unfold tiltMean tiltIntegral
  simp only [one_mul]
  rw [←mul_div_assoc]
  congr 1
  convert he using 1
  · congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  · apply integral_congr_ae
    exact ae_of_all _ fun x => by ring

lemma unitSphere_gibbs_replica_tangent (n : ℕ)
    {H : Spin (n+1)→ℝ} (hH : ContDiff ℝ 1 H) {G : ℝ→ℝ} (hG : ContDiff ℝ 1 G) :
    (n:ℝ)*gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => H x.val) 2
      (fun x => spinOverlap (x 0) (x 1)*G (spinOverlap (x 0) (x 1))) =
    gibbsReplicaMean (unitSphereLaw (n+1)) (fun x => H x.val) 2
      (fun x => deriv G (spinOverlap (x 0) (x 1))*(1-spinOverlap (x 0) (x 1)^2)+
        G (spinOverlap (x 0) (x 1))*fderiv ℝ H (x 0).val
          ((x 1).val-spinOverlap (x 0) (x 1) • (x 0).val)) := by
  let L : NormalizedSpin (n+1)×NormalizedSpin (n+1)→ℝ :=
    fun x => spinOverlap x.1 x.2*G (spinOverlap x.1 x.2)
  let R : NormalizedSpin (n+1)×NormalizedSpin (n+1)→ℝ :=
    fun x => deriv G (spinOverlap x.1 x.2)*(1-spinOverlap x.1 x.2^2)+
      G (spinOverlap x.1 x.2)*fderiv ℝ H x.1.val (x.2.val-spinOverlap x.1 x.2 • x.1.val)
  have hLc : Continuous L := by dsimp [L,spinOverlap]; fun_prop
  have hRc : Continuous R := by
    have hdG := hG.continuous_deriv (by norm_num : 1≤(1:WithTop ℕ∞))
    have hdH := hH.continuous_fderiv (by norm_num)
    dsimp [R,spinOverlap]
    fun_prop
  have hHc : Continuous (fun x : NormalizedSpin (n+1) => H x.val) := hH.continuous.comp continuous_subtype_val
  have hi := continuous_integrable_compact (μ:=unitSphereLaw (n+1)) (Real.continuous_exp.comp hHc)
  have hi' : Integrable (fun x : NormalizedSpin (n+1) => Real.exp (1*H x.val)) (unitSphereLaw (n+1)) := by
    simpa only [one_mul,Function.comp_def] using hi
  let := tilt_law_probability_of_integrable (unitSphereLaw (n+1)) hi'
  change (n:ℝ)*gibbsReplicaMean _ _ 2 (fun x => L (x 0,x 1))=gibbsReplicaMean _ _ 2 (fun x => R (x 0,x 1))
  rw [gibbsReplicaMean_pair_integral _ hHc.measurable hi L hLc.measurable,
    gibbsReplicaMean_pair_integral _ hHc.measurable hi R hRc.measurable,
    integral_prod_symm _ (continuous_integrable_compact hLc),
    integral_prod_symm _ (continuous_integrable_compact hRc),←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun y => unitSphere_gibbs_tangent_mean n y hH hG

end SphericalPerceptronFreeEnergy
end

end OAI
