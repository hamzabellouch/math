import OAI.MeasureTheory.Falconer.Incidence.PublishedFurstenberg
import Mathlib.Tactic

namespace OAI

/-! Restriction and nonemptiness consequences for the normalized finite sets
appearing in the published planar incidence statement. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem finite_ball_bound_card_lower {δ s K : ℝ} {P : Finset (Space 2)}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : P.Nonempty)
    (hball : NormalizedFiniteBallBound δ s K P) :
    1 ≤ K*δ^s*(P.card : ℝ) := by
  obtain ⟨x,hx⟩ := hP
  have hx' : x ∈ P.filter (fun y => dist y x ≤ δ) := by simp [hx,hδ.le]
  have hc : 1 ≤ (P.filter (fun y => dist y x ≤ δ)).card :=
    Finset.one_le_card.mpr ⟨x,hx'⟩
  have hcR : (1 : ℝ) ≤ (P.filter (fun y => dist y x ≤ δ)).card := by exact_mod_cast hc
  exact hcR.trans (hball x δ le_rfl hδ1)

theorem normalized_finite_ball_bound_subset {δ s K C : ℝ}
    {P S : Finset (Space 2)} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hS : S ⊆ P) (hsize : (P.card : ℝ) ≤ C*(S.card : ℝ))
    (hball : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound δ s (K*C) S := by
  intro z r hdr hr1
  have hsub : S.filter (fun x => dist x z ≤ r) ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  calc
    _ ≤ ((P.filter (fun x => dist x z ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K*r^s*(P.card : ℝ) := hball z r hdr hr1
    _ ≤ K*r^s*(C*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hdr) _))
    _ = _ := by ring

theorem finiteSeparatedAt_subset {δ : ℝ} {P S : Finset (Space 2)}
    (hS : S ⊆ P) (hP : FiniteSeparatedAt δ P) : FiniteSeparatedAt δ S :=
  fun x hx y hy hxy => hP x (hS hx) y (hS hy) hxy

end Falconer

end OAI
