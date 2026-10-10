import OAI.NumberTheory.Jacobsthal.Sieve.ResidueCountDifference

namespace OAI

namespace Erdos970


namespace NumberTheoryLean.JacobsthalSourceRounding

theorem floor_length_bounds {x l L : ℝ} (hx : 4 ≤ x) (hl : 0 < l)
    (hlL : l ≤ L) (hLl : L ≤ 2*l) :
    x^2/8 ≤ (⌊(x*l)^2/L^2⌋₊:ℝ) ∧ (⌊(x*l)^2/L^2⌋₊:ℝ) ≤ x^2 := by
  have hL : 0 < L := hl.trans_le hlL
  have hl2 : 0 < l^2 := sq_pos_of_pos hl
  have hL2 : 0 < L^2 := sq_pos_of_pos hL
  have hlow : x^2/4 ≤ (x*l)^2/L^2 := by
    calc
      _ = (x*l)^2/(2*l)^2 := by field_simp [hl.ne']; ring
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg _) hL2 (by nlinarith)
  have hu : (x*l)^2/L^2 ≤ x^2 := by
    calc
      _ ≤ (x*l)^2/l^2 := div_le_div_of_nonneg_left (sq_nonneg _) hl2 (by nlinarith)
      _ = _ := by field_simp [hl.ne']
  have hfloor := Nat.floor_le (div_nonneg (sq_nonneg (x*l)) (sq_nonneg L))
  have hround := Nat.lt_floor_add_one ((x*l)^2/L^2)
  constructor
  · have hs : 16 ≤ x^2 := by nlinarith
    linarith
  · exact hfloor.trans hu

theorem floor_cutoff_bounds {top : ℝ} (htop : 2 ≤ top) :
    top/2 ≤ (⌊top⌋₊:ℝ) ∧ (⌊top⌋₊:ℝ) ≤ top ∧
      top < (⌊top⌋₊:ℝ)+1 ∧ (⌊top⌋₊:ℝ)+1 ≤ 2*top := by
  have hu := Nat.floor_le (by linarith : 0 ≤ top)
  have hl := Nat.lt_floor_add_one top
  exact ⟨by linarith,hu,hl,by linarith⟩
end NumberTheoryLean.JacobsthalSourceRounding


end Erdos970

end OAI
