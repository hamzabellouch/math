import Mathlib
import OAI.Analysis.BiholderTransport.Duality.DualVariation

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace WeakMTWTransport
section AEDual
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

omit [MeasurableSpace M] [BorelSpace M] in
lemma boundedCTransform_perturbation_lipschitz (v f : M →ᵇ ℝ) (x : M) :
    LipschitzWith ‖f‖₊ (fun t : ℝ => boundedCTransform (v+t • f) x) := by
  apply LipschitzWith.of_dist_le_mul
  intro t s
  have hp := BoundedContinuousFunction.dist_coe_le_dist
    (f := boundedCTransform (v+t • f)) (g := boundedCTransform (v+s • f)) x
  apply hp.trans
  have H := boundedCTransform_nonexpansive.dist_le_mul (v+t • f) (v+s • f)
  simp only [NNReal.coe_one,one_mul] at H
  refine H.trans_eq ?_
  rw [dist_eq_norm,add_sub_add_left_eq_sub,← sub_smul t s f,norm_smul,Real.norm_eq_abs,Real.dist_eq]
  exact mul_comm _ _

lemma dual_minimum_integral_eq_ae (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (v : M →ᵇ ℝ) (T : M → M)
    (hT : AEMeasurable T mu)
    (hfib : ∀ᵐ x ∂mu, contactGap (boundedCTransform v) v x (T x)=0 ∧
      ∀ y, contactGap (boundedCTransform v) v x y=0 → y=T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0≤contactGap a b x y) →
      dualObjective mu nu (boundedCTransform v,v)≤dualObjective mu nu (a,b))
    (f : M →ᵇ ℝ) : (∫ x, f (T x) ∂mu)=∫ y,f y ∂nu := by
  have hmeas : AEStronglyMeasurable (fun x => -f (T x)) mu :=
    (f.continuous.measurable.comp_aemeasurable hT).aestronglyMeasurable.neg
  have hdiff : ∀ᵐ x ∂mu, HasDerivAt
      (fun t : ℝ => boundedCTransform (v+t • f) x) (-f (T x)) 0 := by
    filter_upwards [hfib] with x hx
    exact boundedCTransform_perturbation_hasDerivAt v f hx.1 hx.2
  have hlip : ∀ᵐ x ∂mu, LipschitzOnWith (Real.nnabs ‖f‖)
      (fun t : ℝ => boundedCTransform (v+t • f) x) univ := by
    filter_upwards [] with x
    simpa only [show Real.nnabs ‖f‖ = ‖f‖₊ from by ext; simp] using (boundedCTransform_perturbation_lipschitz v f x).lipschitzOnWith
  obtain ⟨_,hder⟩ := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun t x => boundedCTransform (v+t • f) x)
    (F' := fun x => -f (T x)) (bound := fun _ => ‖f‖)
    (s := univ) (mem_of_superset (Filter.univ_mem) (by simp))
    (Filter.Eventually.of_forall fun t => (boundedCTransform (v+t • f)).continuous.aestronglyMeasurable)
    (by simpa only [zero_smul,add_zero] using (boundedCTransform v).integrable mu)
    hmeas hlip (integrable_const _) hdiff
  have hlin : HasDerivAt (fun t : ℝ => ∫ y, (v+t • f) y ∂nu) (∫ y,f y ∂nu) 0 := by
    have H := (hasDerivAt_const (0:ℝ) (∫ y,v y ∂nu)).add
      ((hasDerivAt_id (0:ℝ)).mul_const (∫ y,f y ∂nu))
    simpa only [Pi.add_def,Pi.add_apply,id_eq,zero_add,one_mul,BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply,smul_eq_mul,integral_add (v.integrable nu)
      ((f.integrable nu).const_mul _),integral_const_mul] using H
  have hsum := hder.add hlin
  have hlocal : IsLocalMin (fun t : ℝ => (∫ x,boundedCTransform (v+t • f) x ∂mu)+
      ∫ y,(v+t • f) y ∂nu) 0 := by
    filter_upwards [] with t
    simpa only [zero_smul,add_zero,dualObjective] using
      hmin (boundedCTransform (v+t • f)) (v+t • f)
        (cTransform_gap_nonneg (v+t • f).continuous)
  have H := hlocal.hasDerivAt_eq_zero hsum
  rw [integral_neg] at H
  linarith

lemma dual_minimum_pushforward_ae (mu nu : Measure M) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (v : M →ᵇ ℝ) (T : M → M)
    (hT : AEMeasurable T mu)
    (hfib : ∀ᵐ x ∂mu, contactGap (boundedCTransform v) v x (T x)=0 ∧
      ∀ y, contactGap (boundedCTransform v) v x y=0 → y=T x)
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0≤contactGap a b x y) →
      dualObjective mu nu (boundedCTransform v,v)≤dualObjective mu nu (a,b)) :
    Measure.map T mu=nu := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT f.continuous.aestronglyMeasurable]
  exact dual_minimum_integral_eq_ae mu nu v T hT hfib hmin f

end AEDual
end WeakMTWTransport

end

end

end

end OAI
