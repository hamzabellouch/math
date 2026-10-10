import OAI.Analysis.CircleDomains.Sobolev.L2DominatingSubsequence
import OAI.Analysis.CircleDomains.Probability.PhysicalLineFubini
import OAI.Analysis.CircleDomains.Sobolev.SobolevConformalTransport
import OAI.Analysis.CircleDomains.Sobolev.SmoothCutoffLinePayment

namespace OAI

/-! A continuous compact Sobolev function admits an actual L² payment
for all intervals on almost every coordinate line. Strong mollification
and a summably convergent subsequence supply the payment. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem smooth_line_increment_payment_ae {f g : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) {x y : ℝ}
    (hg : IntervalIntegrable g volume x y)
    (hb : ∀ᵐ t ∂volume, |deriv f t| ≤ g t) :
    |f x-f y| ≤ ∫ t in uIoc x y, g t := by
  have hi : IntervalIntegrable (deriv f) volume x y :=
    hf.continuous_deriv_one.intervalIntegrable x y
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun z (_ : z ∈ uIcc y x) => hf.differentiable_one z) hi.symm
  rw [← he,← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  rw [uIoc_comm y x]
  apply integral_mono_ae hi.norm.def' hg.def'
  exact ae_restrict_of_ae hb

 theorem sobolev_typical_line_payment {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∃ P : EuclideanPlane → ℝ, Measurable P ∧ (∀ z, 0 ≤ P z) ∧ MemLp P 2 volume ∧
      ∀ᵐ y ∂volume, LocallyIntegrable (fun t => P (physicalCoordinateLine i y t)) volume ∧
        ∀ x z : ℝ, |u (physicalCoordinateLine i y x)-u (physicalCoordinateLine i y z)| ≤
          ∫ t in uIoc x z, P (physicalCoordinateLine i y t) := by
  have hg : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  obtain ⟨σ,P,hσ,hP,hP0,hPL,hdom⟩ := exists_L2_dominating_subsequence
    (fun n => planarMollification_partial_memLp W hs n i) hg
    (planarMollification_tendsto_gradient_L2 W i)
  refine ⟨P,hP,hP0,hPL,?_⟩
  filter_upwards [memLp_physicalCoordinateLine_ae hP hPL i,
    ae_ae_physicalCoordinateLine hdom i] with y hy hd
  have hloc := hy.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  refine ⟨hloc,fun x z => ?_⟩
  have hpay (n : ℕ) :
      |planarMollification u (σ n) (physicalCoordinateLine i y x)-
       planarMollification u (σ n) (physicalCoordinateLine i y z)| ≤
        ∫ t in uIoc x z, P (physicalCoordinateLine i y t) := by
    have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
    have hf : ContDiff ℝ 1 (planarMollification u (σ n)) :=
      (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) (σ n)).of_le (by simp)
    apply smooth_line_increment_payment_ae (hf.comp ((physicalCoordinateLine_contDiff i y).of_le (by simp)))
      (intervalIntegrable_iff.mpr ((hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc))
    filter_upwards [hd] with t ht
    simpa only [Function.comp_def,physicalCoordinateLine_deriv hf] using ht n
  exact le_of_tendsto (((planarMollification_tendsto_of_continuous hu _).comp hσ).sub
    ((planarMollification_tendsto_of_continuous hu _).comp hσ)).abs (Eventually.of_forall hpay)

end CircleDomainRigidity

end

end OAI
