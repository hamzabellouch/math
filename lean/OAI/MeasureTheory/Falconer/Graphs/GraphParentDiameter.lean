import OAI.MeasureTheory.Falconer.Graphs.GraphNonedgeGradient

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_two_parent_diameter (X Y : DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    {x y : Plane} (hx : x ∈ X.carrier ∪ Y.carrier) (hy : y ∈ X.carrier ∪ Y.carrier) :
    dist x y ≤ 2004*(2:ℝ)^(-a) := by
  have cross {x y : Plane} (hx : x ∈ X.carrier) (hy : y ∈ Y.carrier) :
      dist x y ≤ 2004*(2:ℝ)^(-a) := by
    have h₁ := X.dist_le hX.le hx (X.center_mem hX)
    have h₂ := Y.dist_le hY.le (Y.center_mem hY) hy
    have ht := dist_triangle4 x X.center Y.center y
    linarith
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have ht := X.dist_le hX.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith
  · exact cross hx hy
  · rw [dist_comm]; exact cross hy hx
  · have ht := Y.dist_le hY.le hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    linarith

theorem dyadic_four_center_differences (X Y : DyadicSquare) (P : Fin 4 → DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    (hP : ∀ i, 0 < (P i).side) (hparent : ∀ i, (P i).carrier ⊆ X.carrier ∪ Y.carrier)
    (i j : Fin 4) : ‖(P i).center-(P j).center‖ ≤ 2004*(2:ℝ)^(-a) := by
  simpa only [dist_eq_norm] using dyadic_two_parent_diameter X Y hX hY hXa hYa hsep
    (hparent i ((P i).center_mem (hP i))) (hparent j ((P j).center_mem (hP j)))

def graphSlotParent (distance : Bool) (X Y : DyadicSquare) (l : Fin 4) : DyadicSquare :=
  if distance then (if l = 0 ∨ l = 3 then X else Y) else (if l.val < 2 then X else Y)

theorem graph_source_parent_center_bounds (distance : Bool) (X Y : DyadicSquare)
    (P : Fin 4 → DyadicSquare) {a : ℝ}
    (hX : 0 < X.side) (hY : 0 < Y.side)
    (hXa : X.side ≤ (2:ℝ)^(-a)) (hYa : Y.side ≤ (2:ℝ)^(-a))
    (hsep : distance = true → dist X.center Y.center ≤ 2000*(2:ℝ)^(-a))
    (hP : ∀ l, 0 < (P l).side)
    (hparent : ∀ l, (P l).carrier ⊆ (graphSlotParent distance X Y l).carrier) :
    ‖(P 0).center-(P 1).center‖ ≤ 2004*(2:ℝ)^(-a) ∧
    ‖(P 2).center-(P 3).center‖ ≤ 2004*(2:ℝ)^(-a) := by
  have hm (l : Fin 4) := hparent l ((P l).center_mem (hP l))
  cases distance
  · have h₀ := hm 0
    have h₁ := hm 1
    have h₂ := hm 2
    have h₃ := hm 3
    norm_num [graphSlotParent] at h₀ h₁ h₂ h₃
    have hx := X.dist_le hX.le h₀ h₁
    have hy := Y.dist_le hY.le h₂ h₃
    rw [dist_eq_norm] at hx hy
    have hp : 0 < (2:ℝ)^(-a) := by positivity
    constructor <;> linarith
  · have hu : ∀ l, (P l).carrier ⊆ X.carrier ∪ Y.carrier := by
      intro l x hx
      have hh := hparent l hx
      by_cases hl : l = 0 ∨ l = 3
      · exact Or.inl (by simpa [graphSlotParent,hl] using hh)
      · exact Or.inr (by simpa [graphSlotParent,hl] using hh)
    exact ⟨dyadic_four_center_differences X Y P hX hY hXa hYa (hsep rfl) hP hu 0 1,
      dyadic_four_center_differences X Y P hX hY hXa hYa (hsep rfl) hP hu 2 3⟩

end PlanarFalconer

end OAI
