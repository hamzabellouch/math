import OAI.InformationTheory.QuantumCircuit.ConditionalParity
import OAI.InformationTheory.QuantumCircuit.PauliExpansion
import OAI.InformationTheory.QuantumCircuit.LowDegreePropagation
import OAI.InformationTheory.QuantumCircuit.ProductStateBasis

namespace OAI

/-! Low-degree propagation and pruning for regular quantum trajectories. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

theorem low_degree_propagation_unconditional
    (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (ψ : ∀ ν, State (m ν)) (hψ : ∀ ν, ‖ψ ν‖ ≤ 1)
    (hreg : RegularTrajectory m l ψ)
    {k K : ℝ} (hk : 0 < k) (hkK : k < K) (hK : K < 1) :
    ∀ᶠ ν in atTop, ∀ E : Operator (m ν),
      HasDegreeLE E ((m ν : ℝ)^k) → ‖E‖ ≤ Real.exp ((m ν : ℝ)^k) →
      ∃ E' : Operator (m ν), HasDegreeLE E' ((m ν : ℝ)^K) ∧
        ‖E'‖ ≤ Real.exp ((m ν : ℝ)^K) ∧
        ‖act (evolution (l ν)) (act E (ψ ν)) -
          act E' (act (evolution (l ν)) (ψ ν))‖ ≤ Real.exp (-((m ν : ℝ)^k)) :=
  low_degree_propagation published_pauli_expansion published_product_spectral_resolution
    d m hm l hl ψ hψ hreg hk hkK hK

theorem regular_pruning_of_factors
    (d : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : ∀ ν, 1 ≤ m ν)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (hs : ∀ ν, NonemptyGateSupports (l ν))
    (a : ∀ ν, Fin (m ν) → Bit → ℂ)
    (ha : ∀ ν i, ∑ b, Complex.normSq (a ν i b) = 1) :
    RegularTrajectory m (fun ν => pruneCircuit (l ν) (productVector (a ν)))
      (fun ν => productVector (a ν)) ∧
    (∀ ν, (pruneCircuit (l ν) (productVector (a ν))).length = (l ν).length) ∧
    (∀ ν, ‖act (evolution (l ν)) (productVector (a ν)) -
      act (evolution (pruneCircuit (l ν) (productVector (a ν)))) (productVector (a ν))‖ ≤
        2 * ((l ν).length : ℝ) * (m ν : ℝ)^(-2 : ℝ)) :=
  regular_pruning_unconditional d m hm hN l hl hs
    (fun ν => ProductInput.ofFactors (a ν) (ha ν))

end QAC

end

end OAI
