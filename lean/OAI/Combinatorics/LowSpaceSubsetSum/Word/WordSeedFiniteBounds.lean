import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedScalarBounds

namespace OAI

/-! # Polynomial cost of a bounded finite-range draw -/

namespace LowSpaceSubsetSum.WordSeedScalarBounds

open WordSeedMeasured

variable {n : ℕ}

theorem fin_bounded_scale (I : Instance n) (hn : 10000 ≤ n) (D : ℕ) [NeZero D]
    (hD : Nat.clog 2 D ≤ 3*n) (w : ℕ) (hw : Nat.clog 2 D ≤ w) :
    (fin w n D hw).Bounded (inputScale I^5) (inputScale I^5) (inputScale I^5) := by
  let u := inputScale I
  have hu : 10000 ≤ u := by dsimp only [u,inputScale]; omega
  have hn3 : n^3 ≤ u^3 := Nat.pow_le_pow_left (by dsimp only [u,inputScale]; omega) 3
  have hnu : n ≤ u^3 := by
    have h := Nat.pow_le_pow_right (by omega : 1 ≤ u) (by decide : 1 ≤ 3)
    simp only [Nat.pow_one] at h
    have hn' : n ≤ u := by dsimp only [u,inputScale]; omega
    exact hn'.trans h
  have hone : 1 ≤ u^3 := by omega
  have hpoly : 45*u^3 ≤ u^5 := by
    calc
      _ ≤ u*u^3 := Nat.mul_le_mul_right _ (by omega)
      _ = u^4 := by ring
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hwork : 13*n^3+5*Nat.clog 2 D+17 ≤ u^5 := by
    apply le_trans _ hpoly
    omega
  have hc := scalar_cells_le I hn
  exact bounded_mono _ (fin_bounded w n D hw) hwork
    ((show 2*n^3+104 ≤ 2*n^3+124 by omega).trans hc.1)
    ((show n^3+18 ≤ n^3+28 by omega).trans hc.2)

end LowSpaceSubsetSum.WordSeedScalarBounds

end OAI
