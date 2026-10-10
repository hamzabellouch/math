import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.TestChain
import OAI.Geometry.WeakHessian.LocalBounds.GlobalTestAverage

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile127
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_test_cutoff_of_compact_lipschitz {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (hfc : HasCompactSupport f) :
    ∃ χ : X → ℝ,IsTestFunction m χ ∧ HasCompactSupport χ ∧
      (∀ x,0 ≤ χ x ∧ χ x ≤ 1) ∧ tsupport χ ⊆ tsupport f ∧
      (∀ x,f x = 1 → χ x = 1) ∧
      ∃ B : ℝ,∀ᵐ x ∂m,|laplacian m χ x| ≤ B := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hf2 : MemLp f 2 m := hf.continuous.memLp_of_hasCompactSupport hfc
  obtain ⟨gs,hgs,hgl,hgb,hgz,hgu,us,hge,hus⟩ :=
    hrcd.exists_global_test_average_approximation hN hfull hfin o hf hfc hf2
  have HH := Metric.tendstoUniformly_iff.mp hgu (1/4) (by norm_num)
  obtain ⟨n,hn⟩ := HH.exists
  let φ : ContDiffBump (1:ℝ) := ⟨1/4,1/2,by norm_num,by norm_num⟩
  have hφ : ContDiff ℝ 3 (φ : ℝ → ℝ) := φ.contDiff
  have hφ2 : ContDiff ℝ 2 (deriv (φ : ℝ → ℝ)) := hφ.deriv'
  have hφ1 : ContDiff ℝ 1 (deriv (deriv (φ : ℝ → ℝ))) := hφ2.deriv'
  obtain ⟨C,hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport hφ (by norm_num)
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport.deriv hφ2 (by norm_num)
  obtain ⟨E,hE⟩ := ContDiff.lipschitzWith_of_hasCompactSupport φ.hasCompactSupport.deriv.deriv hφ1 (by norm_num)
  have hφ0 : φ 0 = 0 := φ.zero_of_le_dist (by norm_num [φ,Real.dist_eq])
  obtain ⟨B,hB⟩ := hgb n
  obtain ⟨hχ,A,hA⟩ := hrcd.test_comp_contDiff_bounded_laplacian hN hfull hfin o (hgs n) hB hφ hC hD hE hφ0
  have hsupp : tsupport (φ ∘ gs n) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra hxt
    have hf0 := image_eq_zero_of_notMem_tsupport hxt
    have hh := hn x
    rw [hf0,dist_zero_left,Real.norm_eq_abs] at hh
    apply hx
    apply φ.zero_of_le_dist
    change (1/2:ℝ) ≤ dist (gs n x) 1
    rw [Real.dist_eq,abs_of_neg (by linarith [le_abs_self (gs n x)] : gs n x-1<0)]
    linarith [le_abs_self (gs n x)]
  refine ⟨φ ∘ gs n,hχ,hfc.of_isClosed_subset (isClosed_tsupport _) hsupp,
    fun x => ⟨φ.nonneg,φ.le_one⟩,hsupp,?_,A,hA⟩
  intro x hx
  apply φ.one_of_mem_closedBall
  have hh := hn x
  rw [hx,Real.dist_eq] at hh
  change |gs n x-1| ≤ (1/4:ℝ)
  simpa only [abs_sub_comm] using hh.le
end WeakHessian

end
end InlinedFile127

end OAI
