import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

theorem integrable_sum_normed {α E ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] [Fintype ι] {f : ι → α → E}
    (hf : ∀ i, Integrable (f i) μ) : Integrable (fun x => ∑ i, f i x) μ :=
  integrable_finsetSum _ (fun i _ => hf i)

end

end OAI
