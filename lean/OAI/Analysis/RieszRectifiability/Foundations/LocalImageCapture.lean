import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.MeasureBounds

namespace OAI

/-!
# Local capture of perturbed images

A displacement bound ensures that points mapping into a given ball originate
in a controlled neighborhood. Capturing that neighborhood by a chart identifies
the image inside the ball, also after restriction by orthogonal projection.
-/

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem image_inter_closedBall_eq_of_bounded_displacement {d : ℕ}
    (f : Ambient d → Ambient d) (A C : Set (Ambient d)) (c : Ambient d)
    (r B : ℝ) (hC : C ⊆ A)
    (hcapture : ∀ x ∈ A, dist x c ≤ r + B → x ∈ C)
    (hmove : ∀ x ∈ A, dist (f x) x ≤ B) :
    (f '' A) ∩ closedBall c r = (f '' C) ∩ closedBall c r := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    refine ⟨⟨x, hcapture x hx ?_, rfl⟩, hy⟩
    have ht := dist_triangle x (f x) c
    rw [dist_comm x (f x)] at ht
    have hm := hmove x hx
    have hb : dist (f x) c ≤ r := hy
    linarith
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨⟨x, hC hx, rfl⟩, hy⟩

theorem image_chart_captures_closedBall {d : ℕ} {U V : Type*}
    (f : Ambient d → Ambient d) (A : Set (Ambient d))
    (g : U → Ambient d) (h : V → Ambient d)
    (P : Submodule ℝ (Ambient d)) (D : Set P) (c : Ambient d) (r B : ℝ)
    (hg : Set.range g ⊆ A)
    (hcapture : ∀ x ∈ A, dist x c ≤ r + B → x ∈ Set.range g)
    (hmove : ∀ x ∈ A, dist (f x) x ≤ B)
    (hrange : Set.range h = (f '' Set.range g) ∩ P.orthogonalProjectionOnto ⁻¹' D)
    (hproject : closedBall c r ⊆ P.orthogonalProjectionOnto ⁻¹' D) :
    (f '' A) ∩ closedBall c r = Set.range h ∩ closedBall c r := by
  rw [image_inter_closedBall_eq_of_bounded_displacement f A (Set.range g) c r B
    hg hcapture hmove, hrange]
  ext y
  constructor
  · intro hy
    exact ⟨⟨hy.1, hproject hy.2⟩, hy.2⟩
  · intro hy
    exact ⟨hy.1.1, hy.2⟩

end

end RieszRectifiability

end OAI
