import OAI.NumberTheory.TotientAsymptotic.CoordinateThreshold

namespace OAI

/-! Effective, uniform form of the coordinate-violation estimate. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

theorem effective_coordinate_count : ∃ C F : ℝ,0 < C ∧ 0 < F ∧
    ∀ X k : ℕ,256 ≤ X → Real.exp (Real.exp 1) ≤ X →
    ∀ ω : ℝ,0 < ω → ω ≤ 1 →
    max 300000000 ((coordinateBudgetConstant F/coordinateDecay ω k)^(4/3:ℝ)) ≤ B X →
    ∀ Q : Finset ℕ,(∀ v ∈ Q,IsTotient v ∧ v ≤ X ∧
      ∃ n : ℕ,0 < n ∧ n.totient=v ∧
        (1+ω)*B X ≤ ∑ j : Fin k,a (j.val+1)*fordPrimeCoordinate n (j.val+1)) →
    (Q.card:ℝ) ≤ C*X/Real.log X*Real.exp (-coordinateDecay ω k*B X) := by
  obtain ⟨C,F,hC,hF,hcount⟩ := coordinate_deviation_count
  refine ⟨C,F,hC,hF,?_⟩
  intro X k hX hx ω hω hω1 hthreshold Q hQ
  have hbig := (le_max_left 300000000 _).trans hthreshold
  have hsq := (le_max_right 300000000 _).trans hthreshold
  have hbudget := coordinate_threshold_budget (by linarith : 1 ≤ B X) hF.le
    (coordinate_decay_pos hω k) hsq
  obtain ⟨hlog,hlarge,hgrid,hsize,habsorb⟩ :=
    coordinate_uniform_budget hbig hω.le hω1 hF.le hbudget
  exact hcount X k hX hx hbig ω hω.le hω1 hlog hlarge hgrid hsize habsorb Q hQ

end TotientAsymptotic

end

end OAI
