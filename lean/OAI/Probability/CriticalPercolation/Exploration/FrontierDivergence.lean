import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.CylinderApproximation
import OAI.Probability.CriticalPercolation.Exploration.SliceExploration

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal symmDiff Topology

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

lemma smallFreshBoundary_approx_bound (hl : G.LocallyFinite) (p : unitInterval)
    (X : Set E) (v : V) (M : ℕ) (H : Set (Set E))
    (hH : MeasurableSet[blockSigma X] H) :
    (1-(p:ℝ))^M * (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary X v M) ≤
      (1 + (1-(p:ℝ))^M) * (G.law p).real (H ∆ G.infiniteEvent v) := by
  have hcost := G.smallFreshBoundary_cost hl p X v M H hH
  have hcover : G.infiniteEvent v ∩ G.smallFreshBoundary X v M ⊆
      (H ∩ G.smallFreshBoundary X v M) ∪ (H ∆ G.infiniteEvent v) := by
    intro ω hω
    by_cases h : ω∈H
    · exact Or.inl ⟨h,hω.2⟩
    · exact Or.inr (Or.inr ⟨hω.1,h⟩)
  have hm := (measureReal_mono hcover (μ := G.law p)).trans
    (measureReal_union_le _ _)
  have he : (G.law p).real (H \ G.infiniteEvent v) ≤
      (G.law p).real (H ∆ G.infiniteEvent v) :=
    measureReal_mono (by intro ω hω; exact Or.inl hω)
  have hr : 0 ≤ (1-(p:ℝ))^M := pow_nonneg (sub_nonneg.mpr p.2.2) _
  nlinarith only [hcost,hm,he,hr]

theorem smallFreshBoundary_probability_tendsto_zero
    (hl : G.LocallyFinite) (p : unitInterval) (hp : (p:ℝ)<1)
    (X : ℕ → Set E) (hX : ∀ S : Finset E, ∀ᶠ n in atTop, (S : Set E) ⊆ X n)
    (v : V) (M : ℕ) :
    Tendsto (fun n => G.law p (G.infiniteEvent v ∩ G.smallFreshBoundary (X n) v M))
      atTop (𝓝 0) := by
  let r : ℝ := (1-(p:ℝ))^M
  have hr : 0 < r := pow_pos (sub_pos.mpr hp) _
  have ht : Tendsto (fun n => (G.law p).real
      (G.infiniteEvent v ∩ G.smallFreshBoundary (X n) v M)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun _ => lt_of_lt_of_le ha measureReal_nonneg)
    · intro b hb
      have hδ : 0 < b*r/(1+r) := div_pos (mul_pos hb hr) (by linarith)
      obtain ⟨S,H,hH,happrox⟩ := exists_finiteCoordinate_approx (fun _ : E => p)
        (G.measurableSet_infiniteEvent v) (ENNReal.ofReal_pos.mpr hδ)
      have hreal : (G.law p).real (H ∆ G.infiniteEvent v) < b*r/(1+r) := by
        have hh := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr happrox
        simpa only [law_const,ENNReal.toReal_ofReal hδ.le,Measure.real,law] using hh
      filter_upwards [hX S] with n hn
      have hh := G.smallFreshBoundary_approx_bound hl p (X n) v M H
        (blockSigma_mono hn _ hH)
      change r * (G.law p).real (G.infiniteEvent v ∩ G.smallFreshBoundary (X n) v M) ≤
        (1+r) * (G.law p).real (H ∆ G.infiniteEvent v) at hh
      have hmul := (mul_lt_mul_of_pos_left hreal (show 0<1+r by linarith))
      rw [mul_div_cancel₀ _ (ne_of_gt (show 0<1+r by linarith))] at hmul
      nlinarith only [hh,hmul,hr]
  have hh := ENNReal.tendsto_ofReal ht
  simpa only [ENNReal.ofReal_zero,Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
