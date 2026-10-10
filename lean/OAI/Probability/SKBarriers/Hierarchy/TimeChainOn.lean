import Mathlib
import OAI.Probability.SKBarriers.Scalar.PositiveTimeChain
import OAI.Probability.SKBarriers.Hierarchy.TimeIncrementBridge

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

structure TimeChainOn (α : ℝ → ℝ) (s t : ℝ) where
  chain : List (ℝ × ℝ≥0)
  duration : (chainDuration chain:ℝ)=t-s
  mass : ∀ p∈chain,p.1∈Icc (0:ℝ) 1
  positive : ∀ p∈chain,0<p.2
  models : TimeChainModels α s chain

def TimeChainOn.append {α : ℝ → ℝ} {s t u : ℝ} (l : TimeChainOn α s t) (r : TimeChainOn α t u) : TimeChainOn α s u where
  chain := l.chain++r.chain
  duration := by rw [chainDuration_append,NNReal.coe_add,l.duration,r.duration]; ring
  mass := by intro p hp; rcases List.mem_append.mp hp with hp|hp; exact l.mass p hp; exact r.mass p hp
  positive := by intro p hp; rcases List.mem_append.mp hp with hp|hp; exact l.positive p hp; exact r.positive p hp
  models := l.models.append (by simpa only [l.duration,add_sub_cancel] using r.models)

theorem TimeChainOn.sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    l.chain.Pairwise (fun p q => p.1≤q.1) := l.models.sorted hα l.positive

theorem TimeChainOn.raw_mass {α : ℝ → ℝ} {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,p.1∈Icc (0:ℝ) 1 := rawTimeChain_mass _ l.mass

theorem TimeChainOn.raw_sorted {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    (rawTimeChain l.chain).Pairwise (fun p q => p.1≤q.1) := rawTimeChain_sorted _ (l.sorted hα)

theorem TimeChainOn.raw_mass_lower {α : ℝ → ℝ} (hα : Monotone α) {s t : ℝ} (l : TimeChainOn α s t) :
    ∀ p∈rawTimeChain l.chain,α s ≤ p.1 := by
  apply rawTimeChain_mass
  intro p hp
  exact (l.models.mass_bounds hα hp (l.positive p hp)).1

theorem exists_quantile_TimeChainOn {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Nonempty (TimeChainOn (quantileCDF k Q) s t) := by
  obtain ⟨l,hd,hm,hp,hmodel⟩ := quantile_interval_chain β Q hQ hs hst ht
  exact ⟨⟨l,hd,hm,hp,hmodel⟩⟩

end SK.Analytic

end
end

end OAI
