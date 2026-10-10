import OAI.Dynamics.EntropyCounterexample.MapLocalEscape
import OAI.Dynamics.EntropyCounterexample.MapGlobalEscape
import OAI.Dynamics.EntropyCounterexample.MapBoundedOrbit
import OAI.Dynamics.EntropyCounterexample.MapFiniteOrbit
import OAI.Dynamics.EntropyCounterexample.ConcreteErasure
import OAI.Dynamics.EntropyCounterexample.MapInfinityAttraction

namespace OAI

noncomputable section
open Filter Set
open scoped Topology OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

def CompletePassageEstimates (D : SphereData) (x : RawManifold) (t₀ : ℝ)
    (z : ℕ → ℂ) : Prop :=
  ∀ k : ℤ, t₀ < 100 * (k : ℝ) →
    ∃ s hi : ℕ, 100 * (k : ℝ) ≤ rawClockLift D x t₀ s ∧
      rawClockLift D x t₀ s < 100 * (k : ℝ) + 74 ∧
      100 * (k : ℝ) + 80 ≤ rawClockLift D x t₀ hi ∧
      (∀ n, s ≤ n → n < hi → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖) ∧
      ∃ j, s ≤ j ∧ j ≤ hi ∧ 1 < ‖z j‖

theorem concrete_orbit_alternatives_of_complete_passages
    (L : ℝ) (hL : 2 < L)
    (hlocal : ∀ (x : RawManifold) (t₀ : ℝ),
      (t₀ : AddCircle (100 : ℝ)) = x.1 →
      ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)) →
      ∀ z : ℕ → ℂ,
      (∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1) →
      CompletePassageEstimates (concreteData L hL) x t₀ z)
    (x : RawManifold) :
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
        (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
      Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 ((0 : ℂ) : Sphere))) ∨
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 (∞ : Sphere)) ∧
      ∀ i : Fin 3, ∀ᶠ n in atTop,
        ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere)) := by
  rcases x with ⟨t, z₀, v⟩
  by_cases hinfty : z₀ = ∞
  · subst z₀
    right
    have hterminal := ConcreteErasure.concreteMap_infty_eventually_zero L hL t v
    refine ⟨?_, fun i => hterminal.mono (fun n hn => hn.2 i)⟩
    apply tendsto_const_nhds.congr
    intro n
    exact (ConstructionInfinityAttraction.raw_iterate_main_infty
      (concreteData L hL) (t, ∞, v) rfl n).symm
  · obtain ⟨t₀, ht₀⟩ := QuotientAddGroup.mk_surjective t
    by_cases hbounded : BddAbove
        (Set.range (rawClockLift (concreteData L hL) (t, z₀, v) t₀))
    · exact Or.inl (concrete_bounded_clock_limits L hL (t, z₀, v) t₀ ht₀ hbounded)
    · obtain ⟨z, hz, _⟩ := exists_finiteMainOrbit (concreteData L hL) (t, z₀, v) hinfty
      have hescape := rawOrbit_norm_tendsto_atTop_of_complete_passages
        (concreteData L hL) (concrete_gate_mem_Icc L hL) (t, z₀, v) t₀ ht₀ z hz
        (hlocal (t, z₀, v) t₀ ht₀ hbounded z hz)
      refine Or.inr ⟨rawOrbit_main_tendsto_infty_of_norm
        (concreteData L hL) (t, z₀, v) z hz hescape, ?_⟩
      intro i
      exact (ConcreteErasure.concreteMap_registers_eventually_zero_of_escape
        L hL (t, z₀, v) z hz hescape).mono (fun n hn => hn i)

theorem concrete_orbit_alternatives (L : ℝ) (hL : 2 < L) (x : RawManifold) :
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).1) atTop
        (𝓝 ((50 : ℝ) : AddCircle (100 : ℝ))) ∧
      Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 ((0 : ℂ) : Sphere))) ∨
    (Tendsto (fun n => ((concreteMap L hL)^[n] x).2.1) atTop
        (𝓝 (∞ : Sphere)) ∧
      ∀ i : Fin 3, ∀ᶠ n in atTop,
        ((concreteMap L hL)^[n] x).2.2 i = ((0 : ℂ) : Sphere)) := by
  apply concrete_orbit_alternatives_of_complete_passages L hL _ x
  intro y t₀ h₀ hunbounded z hz k hk
  exact concrete_unbounded_clock_local_escape L hL y t₀ h₀ hunbounded z hz k hk

end Problem340.Construction

end

end OAI
