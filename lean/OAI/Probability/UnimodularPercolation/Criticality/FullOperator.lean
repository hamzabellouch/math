import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Criticality.FullFiniteness
import OAI.Probability.UnimodularPercolation.Transport.InvariantRoot

namespace OAI

/-! Critical operator boundedness for the full unimodular automorphism group. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
universe u v
variable {V : Type u} {E : Type v}
variable [TopologicalSpace V] [DiscreteTopology V]

theorem critical_bounded_of_graphUnimodular [Infinite V] (G : BondGraph V E)
    (hinj : Function.Injective G) (hconn : Connected G) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G) (x₀ : V)
    (hu : GraphUnimodular G hinj hloc hconn x₀) : OperatorBounded G (pc G) := by
  obtain ⟨n,root,weight,_,hw,hw1,htr,hcov⟩ :=
    exists_rootTransport_of_unimodular G hinj hloc hconn hqt x₀ hu
  have hf := critical_finite_ae_of_transport G hconn hloc hqt hh
    root weight htr hw hw1 hcov
  apply critical_bounded_of_transport_finiteness G hinj hconn hloc hqt hh
    root weight htr hcov hw hw1
  intro i
  filter_upwards [hf] with ω hω
  exact hω (root i)

end Percolation

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}

noncomputable def FullAutUnimodular (G : BondGraph V E)
    (hinj : Function.Injective G) (hloc : LocallyFinite G) (hconn : Connected G)
    (x₀ : V) : Prop := by
  letI : TopologicalSpace V := ⊥
  letI : DiscreteTopology V := ⟨rfl⟩
  exact GraphUnimodular G hinj hloc hconn x₀

theorem critical_operator_fullAut [Infinite V] (G : BondGraph V E)
    (hinj : Function.Injective G) (_hloop : ∀ x, ¬Adj G x x)
    (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (hh : 0 < hV G) (x₀ : V)
    (hu : FullAutUnimodular G hinj hloc hconn x₀) :
    operatorNorm G (pc G) < ⊤ := by
  let : TopologicalSpace V := ⊥
  let : DiscreteTopology V := ⟨rfl⟩
  apply (operatorNorm_lt_top_iff G (pc G)).mpr
  exact critical_bounded_of_graphUnimodular G hinj hconn hloc hqt hh x₀ hu

end Percolation

end OAI
