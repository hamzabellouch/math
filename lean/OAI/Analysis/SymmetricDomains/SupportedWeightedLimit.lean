import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedChartTwoSided
import OAI.Analysis.SymmetricDomains.ClosedMaximizerRelation
import OAI.Analysis.SymmetricDomains.LogarithmicPeakBound
import OAI.Analysis.SymmetricDomains.FiniteUnion

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric Complex
open scoped Classical

def independentSupportCoordinates {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) :
    (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ) := by
  let L := Matrix.mulVecLin (Matrix.of β)
  have hi : Function.Injective L := Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero
      (Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hβ)))
  exact (LinearEquiv.ofBijective L ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv

lemma independentSupportCoordinates_apply {k : ℕ}
    (β : Fin k → Fin k → ℝ) (hβ : LinearIndependent ℝ β) (v : Fin k → ℝ) (i : Fin k) :
    independentSupportCoordinates β hβ v i = ∑ j, β i j*v j := rfl

theorem supported_weighted_limit {r k N : ℕ}
    (Φ : Affine r × Affine k → Affine N) (hΦ : AnalyticAt ℂ Φ 0)
    (U : Set (Affine N)) (O : Set (Affine r × Affine k))
    (hcover : ∀ z ∈ O, ∀ᶠ t : ℝ in 𝓝[>] 0, Φ (weightedScale t z) ∈ U)
    (h : Affine N → ℂ) (hh : ContinuousAt h (Φ 0)) (hh0 : h (Φ 0)=1)
    (hpeak : ∀ y ∈ U, ‖h y‖ ≤ Real.exp (-(‖y-Φ 0‖^2)))
    (ha : AnalyticAt ℂ (fun z => Complex.log (h (Φ z))) 0)
    (β : Fin k → ℝ)
    (hβ : ∀ z, fderiv ℂ (fun z => Complex.log (h (Φ z))) 0 z =
      I*∑ j, (β j : ℂ)*z.2 j) :
    ∃ A : Affine r → ℂ, (∀ z, A (I • z) = -A z) ∧
      ∀ z ∈ O, ‖fderiv ℂ Φ 0 (z.1,0)‖^2 ≤
        (∑ j, β j*(z.2 j).im)-(A z.1).re := by
  obtain ⟨p,hp⟩ := ha
  have hf0 : Complex.log (h (Φ 0))=0 := by rw [hh0,Complex.log_one]
  have hp1 : ∀ z, p 1 (fun _ => z) = I*∑ j, (β j : ℂ)*z.2 j := by
    intro z
    rw [← hβ]
    exact congrArg (fun L => L z) hp.hasFDerivAt.fderiv.symm
  refine ⟨fun z => p 2 (fun _ => (z,0)),?_,?_⟩
  · intro z
    have he : (fun _ : Fin 2 => (I • z,(0 : Affine k))) =
        (fun j : Fin 2 => I • (fun _ : Fin 2 => (z,(0 : Affine k))) j) := by
      funext i
      simp
    change p 2 (fun _ => (I • z,(0 : Affine k))) = -p 2 (fun _ => (z,(0 : Affine k)))
    rw [he,(p 2).map_smul_univ]
    simp
  · intro z hz
    have ht : Tendsto (fun t => Φ (weightedScale t z)) (𝓝[>] (0 : ℝ)) (𝓝 (Φ 0)) :=
      hΦ.continuousAt.tendsto.comp (weightedScale_point_tendsto z)
    have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, h (Φ (weightedScale t z)) ≠ 0 := by
      have hc := hh.tendsto.comp ht
      exact hc.eventually (isOpen_ne.mem_nhds (by rw [hh0]; exact one_ne_zero))
    have hb : ∀ᶠ t : ℝ in 𝓝[>] 0,
        ‖Φ (weightedScale t z)-Φ 0‖^2 ≤ -(Complex.log (h (Φ (weightedScale t z)))).re := by
      filter_upwards [hn,hcover z hz] with t htn htu
      linarith [logarithmic_peak_bound h (fun y => ‖y-Φ 0‖^2) htn (hpeak _ htu)]
    have H := analytic_peak_weighted_bound hp hf0 (fun z => by simp [hp1])
      (hΦ.differentiableAt.hasFDerivAt.restrictScalars ℝ) z hb
    rw [hp1] at H
    simpa only [add_re,I_mul_re,Complex.im_sum,mul_im,ofReal_im,ofReal_re,zero_mul,
      zero_add,neg_add_rev,neg_neg,ContinuousLinearMap.coe_restrictScalars',
      sub_eq_add_neg,add_comm] using H
end Release061

end

end OAI
