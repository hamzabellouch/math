import OAI.Analysis.CircleDomains.Topology.RectifiableSubarcs

namespace OAI

/-! Small image neighborhoods on a finite-cost simple collar admit
actual joining arcs of arbitrarily small cost. Compactness converts
parameter neighborhoods into neighborhoods in the ambient space. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_small_collar_arcs (γ : RectifiablePath X) (g : X → ℝ≥0∞)
    (hg : Measurable g) (hfinite : (∫⁻ t, g (γ.val t) ∂pathLengthMeasure γ) < ∞)
    (r : PathTime) (hsingle : ∀ s, γ.val s = γ.val r → s = r)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ V : Set X, IsOpen V ∧ γ.val r ∈ V ∧
      ∀ x ∈ V ∩ range γ.val, ∀ y ∈ V ∩ range γ.val,
        ∃ ρ : RectifiablePath X, ρ.val ⊥ = x ∧ ρ.val ⊤ = y ∧
          range ρ.val ⊆ range γ.val ∧ (∫⁻ z, g z ∂pathOccupation ρ) < ε := by
  obtain ⟨δ, hδ, hsmall⟩ := exists_small_rectifiable_subarcs γ g hg hfinite r hε
  let K : Set PathTime := {s | δ ≤ dist s r}
  have hK : IsCompact K := (isClosed_le continuous_const (continuous_id.dist continuous_const)).isCompact
  let V := (γ.val '' K)ᶜ
  have hr : γ.val r ∈ V := by
    rintro ⟨s, hs, he⟩
    have hsr := hsingle s he
    subst s
    change δ ≤ dist r r at hs
    exact hδ.not_ge (by simpa only [dist_self] using hs)
  refine ⟨V, (hK.image γ.val.continuous).isClosed.isOpen_compl, hr, ?_⟩
  intro x hx y hy
  obtain ⟨a, ha⟩ := hx.2
  obtain ⟨b, hb⟩ := hy.2
  have had : dist a r < δ := by
    by_contra h
    exact hx.1 ⟨a, le_of_not_gt h, ha⟩
  have hbd : dist b r < δ := by
    by_contra h
    exact hy.1 ⟨b, le_of_not_gt h, hb⟩
  obtain ⟨ρ, hρa, hρb, hρrange, hρcost⟩ := hsmall a b had hbd
  exact ⟨ρ, hρa.trans ha, hρb.trans hb, hρrange, hρcost⟩

end CircleDomainRigidity

end

end OAI
