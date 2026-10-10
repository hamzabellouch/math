import OAI.MeasureTheory.Falconer.Angular.OddAuxiliaryCaps
import OAI.MeasureTheory.Falconer.Estimates.OriginalPairFilter
import OAI.MeasureTheory.Falconer.Measures.LiftedProductPartition

namespace OAI

/-! # Return the odd-dimensional half-integer estimate to the original pair law -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d h : ℕ} {μ : ProbabilityMeasure (Space d)} {α ε : ℝ}
  {f : TwoProjectionFrame μ (h+3) (h+2) α}

namespace TwoProjectionPieces

theorem odd_original_caps_partition (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair p.left p.right) ∧
      CapAvailable p.left p.right Γ ((h:ℝ)+3/2) ∧
      (∀ N, HasBorelProductPartition (Γ N) ((2:ℝ)^(2*((h+3:ℕ):ℝ)*ω*(N:ℝ)))) := by
  obtain ⟨Γ',hΓ',hanti,hpos,_,hcap,hpartition⟩ := p.odd_auxiliary_caps_grid hR hH hF hLW hα hα' hω hω1
  let Γ := liftedPairFilter p.left p.right f.first Γ'
  refine ⟨Γ,liftedPairFilter_measurable _ _ _ hΓ',
    liftedPairFilter_antitone _ _ _ hanti,?_,fun _ => inter_subset_left,?_,?_⟩
  · rw [liftedPairFilter_limit_mass _ _ _ hΓ']
    exact hpos
  · apply CapAvailable.lift_original_pair _ _ _ p.lower_pos f.first_contractive
      (by positivity) hΓ' _ hcap
    intro x hx y hy
    exact p.first_lower (p.left_support hx) (p.right_support hy)

  · intro N
    obtain ⟨T,hT,hTeq⟩ := hpartition N
    exact lifted_pair_has_borel_product_partition p.left p.right f.first
      (centeredUnitCube (h+3)) Γ' hω.le T hT hTeq

theorem odd_original_caps (p : TwoProjectionPieces f ε)
    (hR : PublishedRadialMoment) (hH : PublishedHeavyHyperplanes)
    (hF : PublishedPlanarFurstenberg) (hLW : PublishedFiniteLoomisWhitney)
    (hα : (h:ℝ)+3/2 < α) (hα' : α < (h:ℝ)+2)
    {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ Γ : ℕ → Set (Space d × Space d),
      (∀ N, MeasurableSet (Γ N)) ∧ Antitone Γ ∧
      0 < ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) (⋂ N, Γ N) ∧
      (∀ N, Γ N ⊆ supportPair p.left p.right) ∧
      CapAvailable p.left p.right Γ ((h:ℝ)+3/2) := by
  obtain ⟨Γ,hΓ,hanti,hpos,hsub,hcap,_⟩ :=
    p.odd_original_caps_partition hR hH hF hLW hα hα' hω hω1
  exact ⟨Γ,hΓ,hanti,hpos,hsub,hcap⟩

end TwoProjectionPieces
end Falconer

end OAI
