import OAI.InformationTheory.QuantumCircuit.RetainedRegularity
import OAI.InformationTheory.QuantumCircuit.PruningConstruction

namespace OAI

/-! Regular trajectories obtained by state-dependent pruning. -/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator Topology
open Filter

namespace QAC

theorem pruneCircuit_regular
    (hspec : PublishedProductSpectralResolution) (d : ℕ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (P : ∀ ν, ProductInput (m ν)) :
    RegularTrajectory m (fun ν => pruneCircuit (l ν) (P ν).state) (fun ν => (P ν).state) := by
  intro b h p hb hbh hh hp hph
  filter_upwards [retained_layer_regular hspec d m hm P hb hbh hh hp hph] with ν hν
  intro j R hj S hS hsize
  let W := pruneCircuit (l ν) (P ν).state
  have hlen : (W.take j).length ≤ d := by
    calc
      _ ≤ W.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
      _ = (l ν).length := pruneCircuit_length _ _
      _ ≤ d := hl ν
  have hU : IsCircuit d (evolution (W.take j)) := (evolution_isCircuit _).mono hlen
  exact hν (evolution (W.take j)) hU R
    (pruneCircuit_gate_probability (l ν) (P ν).state j R hj) S hS hsize

theorem regular_pruning
    (hspec : PublishedProductSpectralResolution) (d : ℕ)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : ∀ ν, 1 ≤ m ν)
    (l : ∀ ν, List (AnalyticLayer (m ν))) (hl : ∀ ν, (l ν).length ≤ d)
    (hs : ∀ ν, NonemptyGateSupports (l ν)) (P : ∀ ν, ProductInput (m ν)) :
    RegularTrajectory m (fun ν => pruneCircuit (l ν) (P ν).state) (fun ν => (P ν).state) ∧
    (∀ ν, (pruneCircuit (l ν) (P ν).state).length = (l ν).length) ∧
    (∀ ν, ‖act (evolution (l ν)) (P ν).state -
      act (evolution (pruneCircuit (l ν) (P ν).state)) (P ν).state‖ ≤
        2 * ((l ν).length : ℝ) * (m ν : ℝ)^(-2 : ℝ)) := by
  exact ⟨pruneCircuit_regular hspec d m hm l hl P,
    fun ν => pruneCircuit_length _ _, fun ν => pruneCircuit_error (hN ν) (l ν) (hs ν) _⟩

end QAC

end

end OAI
