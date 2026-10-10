import OAI.Probability.SLE.Stochastic.WienerGridSupport

namespace OAI

/-! Uniform interpolation errors are eventually small on every continuous
path. A countable dense set makes the residual event measurable. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def wienerResidualSet (r : ℝ) : Set (unitInterval → ℝ) :=
  {x | ∀ k : ℕ, |x (denseSeq unitInterval k)| ≤ r}

lemma measurableSet_wienerResidualSet (r : ℝ) : MeasurableSet (wienerResidualSet r) := by
  simp only [wienerResidualSet,Set.ofPred_forall]
  exact MeasurableSet.iInter (fun k => measurableSet_le
    (measurable_pi_apply (denseSeq unitInterval k)).abs measurable_const)

def wienerResidualTube (n : ℕ) (r : ℝ) : Set Target.Driver :=
  {b | ∀ k : ℕ, |wienerGridResidual n (fun t b => b t) (denseSeq unitInterval k) b| ≤ r}

lemma measurableSet_wienerResidualTube (n : ℕ) (r : ℝ) :
    MeasurableSet (wienerResidualTube n r) := by
  simp only [wienerResidualTube,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply measurableSet_le _ measurable_const
  unfold wienerGridResidual wienerGridInterp
  exact ((continuous_eval_const _).measurable.sub
    ((measurable_const.mul (continuous_eval_const _).measurable).add
      (measurable_const.mul (continuous_eval_const _).measurable))).abs

lemma wienerResidualTube_eventually (b : Target.Driver) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ n in atTop, b ∈ wienerResidualTube n r := by
  filter_upwards [wienerGridInterp_uniform b (map_continuous b).continuousOn r hr] with n hn k
  exact hn _

lemma exists_wienerResidualTube_pos (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (r : ℝ) (hr : 0 < r) (N : ℕ) :
    ∃ n, N ≤ n ∧ 0 < W (wienerResidualTube n r) := by
  have : IsProbabilityMeasure W := hW.isGaussianProcess.isProbabilityMeasure
  by_contra! h
  have hzero n (hn : N ≤ n) : W (wienerResidualTube n r)=0 :=
    le_antisymm (h n hn) bot_le
  have hae : ∀ᵐ b ∂W, ∀ n, N ≤ n → b ∉ wienerResidualTube n r := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : N ≤ n
    · exact ((measure_eq_zero_iff_ae_notMem.mp (hzero n hn))).mono (fun b hb _ => hb)
    · exact ae_of_all _ (fun _ h => (hn h).elim)
  obtain ⟨b,hb⟩ := hae.exists
  obtain ⟨n,hn,hmem⟩ := ((eventually_ge_atTop N).and (wienerResidualTube_eventually b r hr)).exists
  exact hb n hn hmem

end SLEExactGauge

end

end OAI
