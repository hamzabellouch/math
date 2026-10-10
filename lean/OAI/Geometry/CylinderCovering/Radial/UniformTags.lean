import OAI.Geometry.CylinderCovering.Radial.ActualEndpoint

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace CylinderCovering.UniformChoice

theorem eventually_forall_of_forall_selection
    {ι : Type*} {X : ι → Type*} {l : Filter ι}
    {P Q : (i : ι) → X i → Prop}
    (hne : ∀ i, ∃ x, P i x)
    (h : ∀ f : (i : ι) → X i, (∀ i, P i (f i)) →
      ∀ᶠ i in l, Q i (f i)) :
    ∀ᶠ i in l, ∀ x, P i x → Q i x := by
  classical
  have hchoice : ∀ i, ∃ x, P i x ∧
      (Q i x → ∀ y, P i y → Q i y) := by
    intro i
    by_cases hbad : ∃ x, P i x ∧ ¬ Q i x
    · obtain ⟨x, hx, hnx⟩ := hbad
      exact ⟨x, hx, fun hqx => False.elim (hnx hqx)⟩
    · obtain ⟨x, hx⟩ := hne i
      refine ⟨x, hx, ?_⟩
      intro _ y hy
      by_contra hny
      exact hbad ⟨y, hy, hny⟩
  choose f hf hgood using hchoice
  filter_upwards [h f hf] with i hi
  exact hgood i hi

end CylinderCovering.UniformChoice

namespace CylinderCovering.RadialRiemann

theorem exists_tagged {a b : ℝ} (hab : a < b) (N : ℕ) :
    ∃ tag : Fin N → ℝ, IsTagged a b N tag := by
  exact ⟨fun i => point a b N i, leftTagged hab N⟩

end CylinderCovering.RadialRiemann

namespace CylinderCovering.RadialSweep

theorem frozenArea_uniform_tags (D : Data) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      |(∑ i : Fin N, frozenArea D N tag i) - weightedArea D| < ε := by
  apply UniformChoice.eventually_forall_of_forall_selection
    (fun N => RadialRiemann.exists_tagged D.interval_nonempty N)
  intro tag htag
  have h := (Metric.tendsto_nhds.mp (frozenArea_tendsto D tag htag)) ε hε
  simpa only [Real.dist_eq] using h

theorem exists_count_frozenArea_uniform_tags (D : Data) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      |(∑ i : Fin N, frozenArea D N tag i) - weightedArea D| < ε := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (frozenArea_uniform_tags D hε)
  refine ⟨max N₀ 1, lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _), ?_⟩
  intro N hN
  exact hN₀ N ((le_max_left _ _).trans hN)

theorem actualCost_uniform_tags (D : Data) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      actualCost D N tag ≤ weightedArea D + ε := by
  apply UniformChoice.eventually_forall_of_forall_selection
    (fun N => RadialRiemann.exists_tagged D.interval_nonempty N)
  intro tag htag
  exact (actual_radial_sweep D tag htag).2.1 ε hε

theorem exists_count_actualCost_uniform_tags (D : Data) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      actualCost D N tag ≤ weightedArea D + ε := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (actualCost_uniform_tags D hε)
  refine ⟨max N₀ 1, lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _), ?_⟩
  intro N hN
  exact hN₀ N ((le_max_left _ _).trans hN)

theorem exists_count_uniform_strict_saving (D : Data) {bound : ℝ}
    (hsaving : weightedArea D < bound) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N, N₀ ≤ N → ∀ tag : Fin N → ℝ,
      RadialRiemann.IsTagged D.α D.β N tag →
      (∑ i : Fin N, frozenArea D N tag i) < bound ∧
        actualCost D N tag < bound := by
  have hε : 0 < (bound - weightedArea D) / 2 := by linarith
  have hboth := (frozenArea_uniform_tags D hε).and (actualCost_uniform_tags D hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hboth
  refine ⟨max N₀ 1, lt_of_lt_of_le (by decide : 0 < 1) (le_max_right _ _), ?_⟩
  intro N hN tag htag
  obtain ⟨hfrozen, hactual⟩ := hN₀ N ((le_max_left _ _).trans hN)
  have hf := (abs_lt.mp (hfrozen tag htag)).2
  have ha := hactual tag htag
  constructor <;> linarith

end CylinderCovering.RadialSweep

end

end OAI
