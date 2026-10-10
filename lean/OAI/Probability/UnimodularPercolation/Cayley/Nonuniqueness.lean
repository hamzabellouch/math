import Mathlib
import OAI.Probability.UnimodularPercolation.Criticality.FullFiniteness
import OAI.Probability.UnimodularPercolation.Cayley.Folner
import OAI.Probability.UnimodularPercolation.Criticality.Phase

namespace OAI

/-! Nonuniqueness of percolation for arbitrary finite symmetric generating sets. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace Percolation
universe u

theorem arbitrary_cayley {Λ : Type u} [Group Λ] [Group.FG Λ]
    (hna : ¬ AmenableGroup Λ) (S : Finset Λ)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set Λ) = ⊤)
    (h1 : 1 ∉ S) :
    OperatorBounded (cayleyGraph S) (pc (cayleyGraph S)) ∧
    pc (cayleyGraph S) < ptwo (cayleyGraph S) ∧
    ptwo (cayleyGraph S) ≤ pu (cayleyGraph S) ∧
    (∃ p₁ p₂ : unitInterval, pc (cayleyGraph S) < p₁ ∧ p₁ < p₂ ∧ p₂ < 1 ∧
      ∀ᵐ labels ∂(labelLaw : Measure (CayleyEdge S → unitInterval)),
        ∀ p ∈ Set.Icc p₁ p₂, (infiniteClusters (cayleyGraph S) (openEdges labels p)).Infinite) ∧
    (∀ p : unitInterval, pc (cayleyGraph S) < p → p < pu (cayleyGraph S) →
      ∀ᵐ ω ∂law p, (infiniteClusters (cayleyGraph S) ω).Infinite) := by
  classical
  let : Infinite Λ := infinite_of_nonamenable hna
  let G := cayleyGraph S
  have hconn : Connected G := cayley_connected S hgen
  have hloc : LocallyFinite G := cayley_locallyFinite S
  have hqt : QuasiTransitive G := cayley_quasiTransitive S
  have hh : 0 < hV G := cayley_hV_pos S hgen hna
  have hsimple : Function.Injective G := cayleyGraph_injective S
  have hloop : ∀ x, ¬ Adj G x x := cayley_loopless S hsym h1
  let : Countable Λ := countable_vertices hloc hconn
  let : Countable (CayleyEdge S) := countable_edges hloc
  let root : Unit → Λ := fun _ => 1
  let weight : Unit → ℝ := fun _ => 1
  have hw : ∀ i, 0 < weight i := fun _ => zero_lt_one
  have hw1 : ∑ i, weight i = 1 := by simp [weight]
  have htr : RootTransport root weight (vertexAut G) := cayley_rootTransport S
  have hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x := by
    intro x
    exact ⟨(), Equiv.mulLeft x, cayley_translation_mem S x, mul_one x⟩
  have hfinite := critical_finite_ae_of_transport G hconn hloc hqt hh root weight htr hw hw1 hcov
  have hb : OperatorBounded G (pc G) := by
    apply critical_bounded_of_transport_finiteness G hsimple hconn hloc hqt hh
      root weight htr hcov hw hw1
    intro i
    filter_upwards [hfinite] with ω hω
    exact hω (root i)
  have hgap := strict_gap_of_critical_bounded G hloc hqt
    (pc_lt_one_of_nonamenable G hconn hloc hqt hh) hb
  have hm := mainConclusion_of_strict_gap G hconn hloc hqt hgap
  exact ⟨hb, hgap, hm.2.2.2.1, hm.2.2.2.2,
    fun p hc hu => infinitely_many_of_pc_lt_lt_pu G hconn hloc hqt p hc hu⟩

end Percolation

end OAI
