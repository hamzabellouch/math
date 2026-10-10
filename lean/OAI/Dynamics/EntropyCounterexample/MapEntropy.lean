import OAI.Dynamics.EntropyCounterexample.RealizedConstruction
import OAI.Dynamics.EntropyCounterexample.ConcreteContinuity
import OAI.Dynamics.EntropyCounterexample.MapTerminalEntropy
import OAI.Dynamics.EntropyCounterexample.TopologicalAttraction
import OAI.Dynamics.EntropyCounterexample.ConcreteErasureLimit

namespace OAI

noncomputable section

open Set Filter
open scoped Topology OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem tendsto_terminalSet_of_coordinate_alternatives (p : ℕ → RawManifold)
    (h : (Tendsto (fun n => (p n).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => (p n).2.1) atTop (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => (p n).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        ∀ i : Fin 3, ∀ᶠ n in atTop, (p n).2.2 i = ((0 : ℂ) : Sphere))) :
    Tendsto p atTop (𝓝ˢ TerminalEntropy.terminalSet) := by
  have hcoords :
      (Tendsto (fun n => (p n).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => (p n).2.1) atTop (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => (p n).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        Tendsto (fun n => (p n).2.2) atTop
          (𝓝 (fun _ : Fin 3 => ((0 : ℂ) : Sphere)))) := by
    rcases h with h | ⟨hmain, hreset⟩
    · exact Or.inl h
    · refine Or.inr ⟨hmain, tendsto_pi_nhds.mpr fun i => ?_⟩
      exact tendsto_const_nhds.congr' (by
        filter_upwards [hreset i] with n hn using hn.symm)
  have htop := TopologicalAttraction.tendsto_two_attractors hcoords
  have hset :
      ({p : RawManifold | p.1 = ((50 : ℝ) : AddCircle (100 : ℝ)) ∧
          p.2.1 = ((0 : ℂ) : Sphere)} ∪
        {p : RawManifold | p.2 = (∞, fun _ => ((0 : ℂ) : Sphere))}) =
      TerminalEntropy.terminalSet := by
    ext x
    simp only [TerminalEntropy.terminalSet, Set.mem_union, Set.mem_ofPred_eq,
      RawInvariantSets.mem_zeroSet_iff, mem_rawInfinitySet_iff]
    rw [show x.2 = (∞, fun _ => ((0 : ℂ) : Sphere)) ↔
        x.2.1 = ∞ ∧ ∀ i, x.2.2 i = ((0 : ℂ) : Sphere) by
      rw [Prod.ext_iff, funext_iff]]
  simpa only [hset] using htop

theorem coverEntropy_realizedMap_eq_zero_of_orbit_alternatives
    (L : ℝ) (hL : 2 < L)
    (horbit : ∀ x : RawManifold,
      (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
          (𝓝 (((0 : ℂ) : Sphere)))) ∨
      (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop (𝓝 (∞ : Sphere)) ∧
        ∀ i : Fin 3, ∀ᶠ n in atTop,
          ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere))) :
    Dynamics.coverEntropy (realizedMap L hL) Set.univ = 0 := by
  apply TerminalEntropy.coverEntropy_eq_zero_of_terminal_attraction L hL
    (continuous_realizedMap L hL (continuous_concreteMap L hL))
    modelHomeomorph.continuous (realizedMap_semiconj L hL)
  intro y
  obtain ⟨x, rfl⟩ := modelHomeomorph.surjective y
  have h := TopologicalAttraction.tendsto_infDist_image modelHomeomorph.continuous
    (tendsto_terminalSet_of_coordinate_alternatives (fun n => (concreteMap L hL)^[n] x) (horbit x))
  simpa only [realizedMap_iterate] using h

theorem coverEntropy_realizedMap_eq_zero_of_main_limits
    (L : ℝ) (hL : 2 < L)
    (horbit : ∀ x : RawManifold,
      (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
          (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
        Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
          (𝓝 (((0 : ℂ) : Sphere)))) ∨
      Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 (∞ : Sphere))) :
    Dynamics.coverEntropy (realizedMap L hL) Set.univ = 0 := by
  apply coverEntropy_realizedMap_eq_zero_of_orbit_alternatives L hL
  intro x
  rcases horbit x with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, fun i => ?_⟩
    exact (ConcreteErasure.concreteMap_registers_eventually_zero_of_main_tendsto_infty
      L hL x h).mono (fun n hn => hn i)

end Problem340.Construction

end

end OAI
