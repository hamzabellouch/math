import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourcePolyDivTendsto
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrefixCoefficientNondvd

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace
open Finset Classical Filter

theorem source_primitive_coefficient_inputs (h : ℕ) (hh : 0<h) (τ C₀ : ℝ)
    (hτ : τ<2) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (s : (sourceSystem B).Specification D h (pathLength B)), s.Primitive →
      ∃ r : (sourceSystem B).Index,
        (r:ℕ) ∣ s.label s.tailStart ∧
        (∀ i : Fin s.length, i<s.tailStart → ¬(r:ℕ) ∣ s.label i) ∧
        (∀ q : (sourceSystem B).Index, (q:ℕ) ∣ s.label s.tailStart →
          (∀ i : Fin s.length, i<s.tailStart → ¬(q:ℕ) ∣ s.label i) →
          ¬((s.extra:ℕ):ℤ) ∣ s.coefficient q s.suffix.val s.length) ∧
        (∀ q : (sourceSystem B).Index,
          (∃ i : Fin s.length, i<s.tailStart ∧ (q:ℕ) ∣ s.label i) →
          ¬((r:ℕ):ℤ) ∣ s.coefficient q 0 s.tailStart.val) := by
  filter_upwards [source_eventually_large h] with B hB
  intro D s hs
  apply s.primitive_coefficient_inputs hs hh hτ (hB.2 s.extra).2
  have hL : pathLength B ≤ ⌊B⌋₊ := Nat.floor_le_floor
    (Real.rpow_le_self_of_one_le hB.1 (by norm_num [rho]))
  have hp := (hB.2 s.extra).1
  simp only [sourceLength] at hp
  omega

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
