import OAI.Analysis.CircleDomains.Transfer.LogarithmicCutCharts
import OAI.Analysis.CircleDomains.Topology.SphereLevels
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! A countable atlas of bounded logarithmic branches on the actual
punctured spherical mask. The closures stay inside that mask. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

theorem exists_countable_bounded_logarithmic_cover
    (F : C(Sphere, ℂ)) (S : Set Sphere) (hS : IsOpen S)
    (h0 : ∀ x ∈ S, F x ≠ 0) (h1 : ∀ x ∈ S, ‖F x‖ ≤ 1) :
    ∃ (T : Set Sphere) (V : Sphere → Set Sphere) (a M : Sphere → ℝ),
      T ⊆ S ∧ T.Countable ∧ S ⊆ ⋃ x ∈ T, V x ∧
      ∀ x ∈ T, IsOpen (V x) ∧ x ∈ V x ∧ closure (V x) ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart (a x) (F y)) (closure (V x)) ∧
        (∀ y ∈ closure (V x), ‖logarithmicCutChart (a x) (F y)‖ ≤ M x) ∧
        (∀ y ∈ closure (V x), 0 ≤ (logarithmicCutChart (a x) (F y)).im) ∧
        (∀ y ∈ closure (V x), diskRayProjection (logarithmicCutChart (a x) (F y)) = F y) := by
  have hlocal (x : Sphere) (hx : x ∈ S) :
      ∃ (V : Set Sphere) (a M : ℝ), IsOpen V ∧ x ∈ V ∧ closure V ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) ∧
        (∀ y ∈ closure V, ‖logarithmicCutChart a (F y)‖ ≤ M) ∧
        (∀ y ∈ closure V, 0 ≤ (logarithmicCutChart a (F y)).im) ∧
        (∀ y ∈ closure V, diskRayProjection (logarithmicCutChart a (F y)) = F y) := by
    have ha : ∃ a : ℝ, x ∈ logarithmicCutDomain F S a := by
      rcases logarithmicCutDomain_cover F S hx with h | h
      · exact ⟨0, h⟩
      · exact ⟨1 / 2, h⟩
    obtain ⟨a, hxa⟩ := ha
    have hW := isOpen_logarithmicCutDomain F F.continuous hS h0 a
    obtain ⟨V, hV, hxV, hVW, _⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := x)) hW (singleton_subset_iff.mpr hxa)
    have hclS : closure V ⊆ S := fun y hy => (hVW hy).1
    have hΨ : ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) := by
      intro y hy
      exact ((continuousAt_logarithmicCutChart a (h0 y (hclS hy))
        (hVW hy).2).comp F.continuous.continuousAt).continuousWithinAt
    obtain ⟨M, hM⟩ := (isClosed_closure.isCompact : IsCompact (closure V)).exists_bound_of_continuousOn hΨ
    exact ⟨V, a, M, hV, hxV (mem_singleton x), hclS, hΨ, hM,
      fun y hy => logarithmicCutChart_nonneg a (h1 y (hclS hy)),
      fun y hy => logarithmicCutChart_projection a (h0 y (hclS hy))⟩
  have hchoice (x : Sphere) : ∃ (V : Set Sphere) (a M : ℝ), x ∈ S →
      IsOpen V ∧ x ∈ V ∧ closure V ⊆ S ∧
        ContinuousOn (fun y => logarithmicCutChart a (F y)) (closure V) ∧
        (∀ y ∈ closure V, ‖logarithmicCutChart a (F y)‖ ≤ M) ∧
        (∀ y ∈ closure V, 0 ≤ (logarithmicCutChart a (F y)).im) ∧
        (∀ y ∈ closure V, diskRayProjection (logarithmicCutChart a (F y)) = F y) := by
    by_cases hx : x ∈ S
    · obtain ⟨V, a, M, h⟩ := hlocal x hx
      exact ⟨V, a, M, fun _ => h⟩
    · exact ⟨∅, 0, 0, fun h => (hx h).elim⟩
  choose V a M hV using hchoice
  obtain ⟨T, hTS, hTc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (s := S) (f := V) (fun x hx => mem_nhdsWithin_of_mem_nhds
      ((hV x hx).1.mem_nhds (hV x hx).2.1))
  exact ⟨T, V, a, M, hTS, hTc, hcover, fun x hx => hV x (hTS hx)⟩

end CircleDomainRigidity

end

end OAI
