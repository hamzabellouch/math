import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateGapBudgetScales

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Filter InitialCharacterScale

theorem eventually_diagonal_gap_budget (B β C BD O K : ℝ) (k : ℕ) {c α : ℝ}
    (hc : 0 < c) (hα : 0 < α) (hBD : diagonalGapThreshold B β C ≤ BD) :
    ∀ᶠ L : ℝ in atTop, ∀j : ℕ, j < k → ∀d : ℝ, d ≤ (wordSize k L : ℝ) →
      Real.exp (-gapSchedule BD k L (j+1)+
        (2 : ℝ)^j*(wordSize k L : ℝ)*(Real.log (depthScale k)+C+Real.log 2)+
        (β+1)*(2 : ℝ)^j*L+(wordSize k L : ℝ)+O)+
        Real.exp (K*L^2-c*Real.exp (α*L)) ≤
      (1/2 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ)) := by
  filter_upwards [eventually_good_diagonal_quarter B β C BD O k hBD,
    eventually_error_diagonal_quarter B K k hc hα] with L hg he
  intro j hj d hd
  calc
    _ ≤ (1/4 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ))+
        (1/4 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ)) :=
      add_le_add (hg j d hd) (he j hj.le d hd)
    _ = _ := by ring

theorem exists_diagonal_gap_budget (B β ρ : ℝ) :
    ∃BD0 : ℝ, 0 < BD0 ∧ ∀BD : ℝ, BD0 ≤ BD → ∀k : ℕ, ∀O K : ℝ,
      ∀c α : ℝ, 0 < c → 0 < α →
      ∀ᶠ L : ℝ in atTop, ∀j : ℕ, j < k → ∀d : ℝ,
        0 ≤ d → d ≤ (wordSize k L : ℝ) →
        Real.exp (-gapSchedule BD k L (j+1)+
          (2 : ℝ)^j*(wordSize k L : ℝ)*
            (Real.log (depthScale k)+(|Real.log ρ|+2)+Real.log 2)+
          (β+1)*(2 : ℝ)^j*L+(wordSize k L : ℝ)+O)+
          Real.exp (K*L^2-c*Real.exp (α*L)) ≤
        (1/2 : ℝ)*Real.exp (-d)*Real.exp (-2*B*(2 : ℝ)^j*(wordSize k L : ℝ)) := by
  refine ⟨diagonalGapThreshold B β (|Real.log ρ|+2),
    diagonalGapThreshold_pos _ _ _,?_⟩
  intro BD hBD k O K c α hc hα
  filter_upwards [eventually_diagonal_gap_budget B β (|Real.log ρ|+2) BD O K k hc hα hBD]
    with L hL
  intro j hj d _ hd
  exact hL j hj d hd

end Ostmann.Characters.DiagonalEstimate

end

end OAI
