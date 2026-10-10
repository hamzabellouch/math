import OAI.MeasureTheory.Falconer.Incidence.BlockDepthBracket

namespace OAI

/-! The selected block immediately above a prescribed integer depth. -/
namespace Falconer.Regularization

theorem blockDepth_upper_bracket {N B i j n : ℕ} (hji : j ≤ i)
    (hlo : blockDepth N B i ≤ n) (hhi : n ≤ blockDepth N B j) :
    ∃ k, j ≤ k ∧ k ≤ i ∧ n ≤ blockDepth N B k ∧ blockDepth N B k ≤ n+B := by
  have hex : ∃ r, r ≤ i-j ∧ n ≤ blockDepth N B (i-r) :=
    ⟨i-j,le_rfl,by simpa only [Nat.sub_sub_self hji] using hhi⟩
  let r := Nat.find hex
  have hr : r ≤ i-j ∧ n ≤ blockDepth N B (i-r) := Nat.find_spec hex
  refine ⟨i-r,by omega,by omega,hr.2,?_⟩
  by_cases hz : r = 0
  · simp only [hz,Nat.sub_zero]
    omega
  · have hr0 : 0 < r := Nat.pos_of_ne_zero hz
    have hprev : blockDepth N B (i-r+1) < n := by
      by_contra hn
      have hmin := Nat.find_min hex (show r-1 < r by omega)
      apply hmin
      refine ⟨by omega,?_⟩
      have he : i-(r-1) = i-r+1 := by omega
      simpa only [he] using (le_of_not_gt hn)
    have hgap := blockDepth_gap N B (i-r)
    have hord := blockDepth_antitone N B (Nat.le_succ (i-r))
    omega

end Falconer.Regularization

end OAI
