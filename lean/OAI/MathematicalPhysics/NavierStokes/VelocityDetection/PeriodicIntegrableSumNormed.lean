import Mathlib

namespace OAI

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
open scoped Topology ContDiff ZeroAtInfty BigOperators

theorem periodic_integrable_sum_normed {α E ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [Fintype ι] {f : ι → α → E}
    (hf : ∀ i, Integrable (f i) μ) : Integrable (fun x => ∑ i, f i x) μ :=
  integrable_finsetSum _ (fun i _ => hf i)

end

end OAI
