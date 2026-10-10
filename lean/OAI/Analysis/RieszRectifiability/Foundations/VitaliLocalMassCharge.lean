import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
A disjoint Vitali selection converts local charges on fivefold enlarged balls into
a comparison between the total mass of a set and the mass of its containing region.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

theorem measure_le_of_local_fivefold_charges {d : ℕ}
    (ν μ : Measure (Ambient d)) (A Ω : Set (Ambient d)) (r : Ambient d → ℝ)
    (R : ℝ) (hpos : ∀ x ∈ A, 0 < r x) (hbound : ∀ x ∈ A, r x ≤ R)
    (hcontained : ∀ x ∈ A, closedBall x (r x) ⊆ Ω) (C : ℝ≥0∞)
    (hcharge : ∀ x ∈ A, ν (A ∩ closedBall x (5 * r x)) ≤ C * μ (closedBall x (r x))) :
    ν A ≤ C * μ Ω := by
  obtain ⟨u, hu, hdisjoint, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall A id r R hbound 5 (by norm_num)
  have hcount : u.Countable := hdisjoint.countable_of_nonempty_interior (by
    intro x hx
    exact ⟨x, ball_subset_interior_closedBall (mem_ball_self (hpos x (hu hx)))⟩)
  let := hcount.to_subtype
  have hcover' : A ⊆ ⋃ x : u, A ∩ closedBall (x : Ambient d) (5 * r x) := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, hx, hxy (mem_closedBall_self (hpos x hx).le)⟩
  have hd : Pairwise (fun x y : u =>
      Disjoint (closedBall (x : Ambient d) (r x)) (closedBall (y : Ambient d) (r y))) := by
    intro x y hxy
    exact hdisjoint x.property y.property (fun h => hxy (Subtype.ext h))
  have hsub : (⋃ x : u, closedBall (x : Ambient d) (r x)) ⊆ Ω :=
    iUnion_subset (fun x => hcontained x (hu x.property))
  calc
    ν A ≤ ν (⋃ x : u, A ∩ closedBall (x : Ambient d) (5 * r x)) := measure_mono hcover'
    _ ≤ ∑' x : u, ν (A ∩ closedBall (x : Ambient d) (5 * r x)) := measure_iUnion_le _
    _ ≤ ∑' x : u, C * μ (closedBall (x : Ambient d) (r x)) :=
      ENNReal.tsum_le_tsum (fun x => hcharge x (hu x.property))
    _ = C * ∑' x : u, μ (closedBall (x : Ambient d) (r x)) :=
      ENNReal.tsum_mul_left
    _ = C * μ (⋃ x : u, closedBall (x : Ambient d) (r x)) := by
      rw [measure_iUnion hd (fun _ => measurableSet_closedBall)]
    _ ≤ C * μ Ω := mul_le_mul_right (measure_mono hsub) C

end

end RieszRectifiability

end OAI
