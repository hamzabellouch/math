import OAI.Analysis.CircleDomains.Sobolev.ExactSobolevLinePayment
import OAI.Analysis.CircleDomains.Sobolev.IntegralPaymentAbsoluteContinuity

namespace OAI

/-! The actual weak partials integrate to coordinate increments on almost
every line; the continuous representative is absolutely continuous there. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma sobolev_coordinate_fundamentalTheorem {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ x z : ℝ,
      (∫ t in x..z, W.weakGrad (physicalCoordinateLine i y t) i) =
        u (physicalCoordinateLine i y z)-u (physicalCoordinateLine i y x) := by
  have hg : MemLp (fun x => W.weakGrad x i) 2 volume := by
    simpa only [Measure.restrict_univ] using W.weakGrad_component_memLp i
  obtain ⟨ρ, P, hρ, hP, _, hPL, hdom⟩ := exists_L2_dominated_ae_subsequence
    (fun n => planarMollification_partial_memLp W hs n i) hg
    (planarMollification_tendsto_gradient_L2 W i)
  have huL : MemLp u 2 volume := by simpa only [Measure.restrict_univ] using W.memLp
  have hfn (n : ℕ) : ContDiff ℝ 1 (planarMollification u (ρ n)) :=
    (planarMollification_smooth (huL.locallyIntegrable (by norm_num)) (ρ n)).of_le (by simp)
  filter_upwards [memLp_physicalCoordinateLine_ae hP hPL i,
    ae_ae_physicalCoordinateLine hdom i] with y hy hd
  apply line_integral_eq_sub_of_dominated_derivatives
    (fun n => (hfn n).comp ((physicalCoordinateLine_contDiff i y).of_le (by simp)))
    (fun t => (planarMollification_tendsto_of_continuous hu _).comp hρ)
    (hy.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  · filter_upwards [hd] with t ht
    intro n
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn n)] using ht.1 n
  · filter_upwards [hd] with t ht
    simpa only [Function.comp_def, physicalCoordinateLine_deriv (hfn _)] using ht.2

lemma sobolev_coordinate_absolutelyContinuous {u : EuclideanPlane → ℝ}
    (hu : Continuous u) (hs : HasCompactSupport u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (i : Fin 2) :
    ∀ᵐ y ∂volume, ∀ a b : ℝ,
      AbsolutelyContinuousOnInterval (fun t => u (physicalCoordinateLine i y t)) a b := by
  filter_upwards [exact_sobolev_line_payment hu hs W i] with y hy
  exact integral_payment_implies_absoluteContinuity
    (fun a b => (hy a b).1) (fun a b => (hy a b).2)

end CircleDomainRigidity

end

end OAI
