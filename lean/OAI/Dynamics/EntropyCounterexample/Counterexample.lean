import OAI.Dynamics.EntropyCounterexample.Definitions
import OAI.Dynamics.EntropyCounterexample.Assembly

namespace OAI

noncomputable section

namespace Problem340

theorem exists_C1_entropy_counterexample :
    ∃ q : ℕ, 0 < q ∧ ∃ f : CounterexampleManifold q → CounterexampleManifold q, ∃ hf : IsC1SelfMap q f, Dynamics.coverEntropy f (Set.univ : Set (CounterexampleManifold q)) = (0 : EReal) ∧ (∃ v : RealSingularHomology 2 (CounterexampleManifold q), v ≠ 0 ∧ realHomologyMap 2 f hf.1 v = (2 : ℝ) • v) ∧ 0 < Real.log (2 : ℝ) ∧ Real.log (2 : ℝ) ≤ Real.log (totalRealHomologySpectralRadius f hf.1) ∧ ¬ Function.Bijective f ∧ 5 ≤ 2 * q + 3 := by
  exact CounterexampleAssembly804.exists_counterexample

end Problem340

end

end OAI
