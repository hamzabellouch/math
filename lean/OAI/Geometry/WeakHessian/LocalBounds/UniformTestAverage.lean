import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.AverageTest
import OAI.Geometry.WeakHessian.LocalBounds.AverageConvergence
import OAI.Geometry.WeakHessian.Calculus.LipschitzPointLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile124
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma lipschitz_tendstoUniformlyOn_compact {ι : Type*} {l : Filter ι}
    {gs : ι → X → ℝ} {g : X → ℝ} {L : ℝ≥0}
    (hg : ∀ i,LipschitzWith L (gs i)) (ht : ∀ x,Tendsto (fun i => gs i x) l (𝓝 (g x)))
    {S : Set X} (hS : IsCompact S) : TendstoUniformlyOn gs g l S := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hl (i : ι) : LipschitzWith L (fun x : S => gs i x) := by
    simpa only [mul_one,Function.comp_def] using (hg i).comp (LipschitzWith.subtype_val S)
  have he := (LipschitzWith.uniformEquicontinuous (fun i (x:S) => gs i x) L hl).equicontinuous
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  apply UniformFun.tendsto_iff_tendstoUniformly.mp
  apply (he.tendsto_uniformFun_iff_pi l (fun x : S => g x)).mpr
  exact tendsto_pi_nhds.mpr fun x => ht x

variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m]

lemma RCD.exists_test_average_approximation {K N : ℝ} (hN : 1 < N)
    (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {f : X → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f)
    (hfc : HasCompactSupport f) (hf2 : MemLp f 2 m) :
    ∃ gs : ℕ → X → ℝ,
      (∀ n,IsTestFunction m (gs n)) ∧
      (∀ n,LipschitzWith (L*⟨Real.exp |K|,(Real.exp_pos _).le⟩) (gs n)) ∧
      (∀ n,∃ B : ℝ,∀ᵐ x ∂m,|laplacian m (gs n) x| ≤ B) ∧
      (∀ n,∀ ε : ℝ,0 < ε → ∃ R : ℝ,0 ≤ R ∧ ∀ x : X,R < dist x o → |gs n x| < ε) ∧
      (∀ S : Set X,IsCompact S → TendstoUniformlyOn gs f atTop S) ∧
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
  refine ⟨gs,hgs,hgl',hgb,hgz,?_,us,hge,hus⟩
  intro S hS
  apply lipschitz_tendstoUniformlyOn_compact hgl' _ hS
  intro x
  exact lipschitz_point_tendsto_of_L2 hfull hfin hgl' hf us _ hge hf2.coeFn_toLp.symm hus x
end WeakHessian

end
end InlinedFile124

end OAI
