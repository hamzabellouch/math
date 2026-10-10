import OAI.Analysis.CircleDomains.Sobolev.PriorityDerivativeError
import OAI.Analysis.CircleDomains.Topology.ConcentratedCutoffs

namespace OAI

/-! The priority formula is smooth off the closed source dust because
its shrinking cutoff supports have a common locally vanishing tail. -/
open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem priorityBlend_contDiffAt {L : List ((E → ℝ) × ℝ)} {X : E → ℝ} {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hL : ∀ e ∈ L, ContDiffAt ℝ ∞ e.1 p) :
    ContDiffAt ℝ ∞ (priorityBlend L X) p := by
  induction L with
  | nil => exact hX
  | cons e L ih =>
    have he := hL e (by simp)
    exact (he.mul contDiffAt_const).add ((contDiffAt_const.sub he).mul
      (ih (fun a ha => hL a (by simp [ha]))))

 theorem priorityInfiniteValue_contDiffAt
    (χ : ℕ → E → ℝ) (c : ℕ → ℝ) (X : E → ℝ) {p : E}
    (hX : ContDiffAt ℝ ∞ X p) (hχ : ∀ n, ContDiffAt ℝ ∞ (χ n) p)
    (hz : ∃ N : ℕ, ∀ᶠ q in 𝓝 p, ∀ n, N ≤ n → χ n q = 0) :
    ContDiffAt ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) p := by
  obtain ⟨N, hN⟩ := hz
  have hL : ∀ e ∈ priorityList χ c N, ContDiffAt ℝ ∞ e.1 p := by
    intro e he
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp he
    exact hχ n
  apply (priorityBlend_contDiffAt hX hL).congr_of_eventuallyEq
  filter_upwards [hN] with q hq
  exact priorityInfiniteValue_eq_finite c X hq

 theorem priorityInfiniteValue_smooth_off_dust
    {B : Set E} (hB : IsClosed B) (b : ℕ → E) (hb : ∀ n, b n ∈ B)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → E → ℝ) (hχ : ∀ n, ContDiff ℝ ∞ (χ n))
    (hs : ∀ n, support (χ n) ⊆ Metric.ball (b n) (r n))
    (c : ℕ → ℝ) (X : E → ℝ) (hX : ContDiffOn ℝ ∞ X Bᶜ) :
    ContDiffOn ℝ ∞ (fun q => priorityInfiniteValue (fun n => χ n q) c (X q)) Bᶜ := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  apply priorityInfiniteValue_contDiffAt χ c X
    ((hX p hp).contDiffAt (hB.isOpen_compl.mem_nhds hp)) (fun n => (hχ n).contDiffAt)
  obtain ⟨V, hV, hpV, N, hN⟩ := concentrated_cutoffs_eventually_zero hB b hb r hr χ hs hp
  exact ⟨N, Filter.mem_of_superset (hV.mem_nhds hpV) (fun q hq n hn => hN n hn q hq)⟩

end CircleDomainRigidity

end

end OAI
