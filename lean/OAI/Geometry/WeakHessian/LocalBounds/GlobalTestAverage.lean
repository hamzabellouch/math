import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.UniformTestAverage
import OAI.Geometry.WeakHessian.LocalBounds.UniformWeightedCZero

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile126
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_global_test_average_approximation {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m) :
    ∃ gs : ℕ → X → ℝ,
      (∀ n,IsTestFunction m (gs n)) ∧
      (∀ n,LipschitzWith (L*⟨Real.exp |K|,(Real.exp_pos _).le⟩) (gs n)) ∧
      (∀ n,∃ B : ℝ,∀ᵐ x ∂m,|laplacian m (gs n) x| ≤ B) ∧
      (∀ n,∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |gs n x| < ε) ∧
      TendstoUniformly gs f atTop ∧
      ∃ us : ℕ → Lp ℝ 2 m,(∀ n,gs n =ᵐ[m] us n) ∧ Tendsto us atTop (𝓝 (hf2.toLp f)) := by
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have ht1 (n : ℕ) : t n ≤ 1 := by
    dsimp [t]
    exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])
  let us (n : ℕ) := (t n)⁻¹ • ∫ s in 0..t n,cheegerHeat hrcd.2 s (hf2.toLp f)
  have ht0 : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall ht⟩
  have hus : Tendsto us atTop (𝓝 (hf2.toLp f)) := (cheegerHeat_average_tendsto hfin hrcd.2 _).comp ht0
  choose gs hgs hgl hge hgb hgz using fun n =>
    hrcd.cheegerHeat_average_test hN hfull hfin hrcd.2 o hf hfc hf2 (ht n)
  have hgl' (n : ℕ) : LipschitzWith (L*⟨Real.exp |K|,(Real.exp_pos _).le⟩) (gs n) := by
    apply (hgl n).weaken
    apply mul_le_mul_of_nonneg_left _ (show 0 ≤ L from zero_le)
    change Real.exp (|K| *t n) ≤ Real.exp |K|
    exact Real.exp_le_exp.mpr (by nlinarith [abs_nonneg K,ht1 n])
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hv : ∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ n,∀ x : X,R < dist x o → |gs n x| < ε := by
    apply lipschitz_uniformly_vanishes_of_expWeighted hfin o
      (fun _ hr => hrcd.1.ball_measure_lower_exp hN hfull hfin o hr) hgl'
    intro a ha
    have hV := lipschitz_mul_dist o a
    have hWf : MemLp (fun x => f x*Real.exp (a*dist x o)) 2 m :=
      (hf.continuous.mul (Real.continuous_exp.comp hV.continuous)).memLp_of_hasCompactSupport hfc.mul_right
    have hWu : MemLp (fun x => hf2.toLp f x*Real.exp (a*dist x o)) 2 m :=
      (memLp_congr_ae (hf2.coeFn_toLp.mul Filter.EventuallyEq.rfl).symm).mp hWf
    let W := ‖hWu.toLp (fun x => hf2.toLp f x*Real.exp (a*dist x o))‖
    refine ⟨(W*Real.exp (a^2))^2,fun n => ?_⟩
    have H := hrcd.1.cheegerHeat_average_weighted hfin o hrcd.2 (hf2.toLp f) hV hWu (ht n)
    have he : (fun x => gs n x*Real.exp (a*dist x o)) =ᵐ[m]
        (fun x => us n x*Real.exp (a*dist x o)) := (hge n).mul Filter.EventuallyEq.rfl
    refine ⟨(memLp_congr_ae he.symm).mp H.1,?_⟩
    rw [integral_congr_ae (he.mono fun x hx => congrArg (fun z : ℝ => z^2) hx)]
    apply H.2.trans
    apply pow_le_pow_left₀ (by positivity) _ 2
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    change |a|^2*t n ≤ a^2
    rw [sq_abs]
    nlinarith [sq_nonneg a,ht1 n]
  have hu : ∀ S : Set X,IsCompact S → TendstoUniformlyOn gs f atTop S := by
    intro S hS
    apply lipschitz_tendstoUniformlyOn_compact hgl' _ hS
    intro x
    exact lipschitz_point_tendsto_of_L2 hfull hfin hgl' hf us _ hge hf2.coeFn_toLp.symm hus x
  refine ⟨gs,hgs,hgl',hgb,hgz,?_,us,hge,hus⟩
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨R,hR,hRgs⟩ := hv (ε/2) (by positivity)
  obtain ⟨S,hS⟩ := hfc.isCompact.isBounded.subset_closedBall o
  have H := Metric.tendstoUniformlyOn_iff.mp (hu (Metric.closedBall o (max R S)) (isCompact_closedBall o _)) ε hε
  filter_upwards [H] with n hn x
  by_cases hx : dist x o ≤ max R S
  · exact hn x hx
  · have hxR : R < dist x o := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hx)
    have hfx : f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hxt
      have hh := hS hxt
      exact hx ((show dist x o ≤ S from hh).trans (le_max_right _ _))
    rw [hfx,dist_zero_left,Real.norm_eq_abs]
    exact (hRgs n x hxR).trans (by linarith)

end WeakHessian

end
end InlinedFile126

end OAI
