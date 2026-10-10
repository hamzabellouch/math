import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.BalancedRyser.Construction.ConstructionRepresentationLemmas
import OAI.Combinatorics.BalancedRyser.Probability.SizeThreshold

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter
open scoped Topology

universe u

theorem balancedCounterexample_of_configuration
    (hdet : DeterministicReduction.{u})
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (C : Configuration F) (ρ : ℝ) (B : ℕ)
    (hq : 4 ≤ Fintype.card F) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hV : C.Valid) (hC : C.Compatible) (hO : C.Occupancy ρ B)
    (hCore : C.CoreConcentration ρ) (hLocal : C.LocalCondition)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    BalancedCounterexample (Fintype.card F) := by
  obtain ⟨H, hI, hN, hCover, _⟩ :=
    hdet F C ρ B hq hρ0 hρ1 hV hC hO hCore hLocal hsize
  exact ⟨H, hI, hN, hCover⟩

theorem mainResult_of_prime_configurations
    (hdet : DeterministicReduction.{0})
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ)
    (hconfiguration : ∀ (q : ℕ) (hq : q.Prime), N ≤ q →
      letI : Fact q.Prime := ⟨hq⟩
      ∃ C : Configuration (ZMod q),
        C.Valid ∧ C.Compatible ∧
        C.Occupancy ρ ⌈Real.log (q : ℝ)⌉₊ ∧
        C.CoreConcentration ρ ∧ C.LocalCondition) : MainResult := by
  obtain ⟨Nsize, hsize⟩ := exists_size_threshold ρ hρ0
  refine ⟨max N Nsize, ?_⟩
  intro q hq hprime
  let : Fact q.Prime := ⟨hprime⟩
  have hN : N ≤ q := (le_max_left N Nsize).trans hq
  have hNs : Nsize ≤ q := (le_max_right N Nsize).trans hq
  obtain ⟨C, hV, hC, hO, hCore, hLocal⟩ := hconfiguration q hprime hN
  obtain ⟨hfour, hlarge⟩ := hsize q hNs
  have hcard : Fintype.card (ZMod q) = q := ZMod.card q
  have h := balancedCounterexample_of_configuration hdet C ρ
    ⌈Real.log (q : ℝ)⌉₊ (by simpa only [hcard] using hfour) hρ0 hρ1
    hV hC hO hCore hLocal (by simpa only [hcard] using hlarge)
  simpa only [hcard] using h

theorem mainResult_of_eventually_prime_configurations
    (hdet : DeterministicReduction.{0})
    (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hconfiguration : ∀ᶠ q : ℕ in atTop, ∀ hq : q.Prime,
      letI : Fact q.Prime := ⟨hq⟩
      ∃ C : Configuration (ZMod q),
        C.Valid ∧ C.Compatible ∧
        C.Occupancy ρ ⌈Real.log (q : ℝ)⌉₊ ∧
        C.CoreConcentration ρ ∧ C.LocalCondition) : MainResult := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hconfiguration
  exact mainResult_of_prime_configurations hdet ρ hρ0 hρ1 N
    (fun q hq hlarge => hN q hlarge hq)

end Balanced

end OAI
