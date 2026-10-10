import OAI.Combinatorics.EditApproximation.Coarse.CoarseGridInvariant

namespace OAI

namespace EditApproximation

 theorem coarseScale_root_grid (B q L j d : ℕ) (allowance : ℚ) (hq : 0 < q)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    (allowance / q).den ∣ coarseCommonDenominator 1 q L B (j + d) := by
  apply (coarse_rat_div_nat_den_dvd allowance q _ hq ha).trans
  refine ⟨(L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add]
  ring

 theorem coarseThreshold_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    (coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  have ht : (coarseChildThreshold B q allowance draw).den ∣ (L * B * q) ^ j * (B * q) := by
    simpa only [coarseChildThreshold, Nat.cast_mul] using
      coarse_rat_div_nat_den_dvd (allowance * ((draw.val + 1 : ℕ) : ℚ)) (B * q) ((L * B * q) ^ j)
        (Nat.mul_pos hB hq) (coarse_rat_mul_nat_den_dvd allowance (draw.val + 1) _ ha)
  apply ht.trans
  refine ⟨q * L * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

 theorem coarseChildAllowance_root_grid (B q L j d : ℕ) (allowance : ℚ) (draw : Fin B)
    (hB : 0 < B) (hq : 0 < q) (hL : 0 < L)
    (ha : allowance.den ∣ (L * B * q) ^ j) :
    ((1 / (L : ℚ)) * coarseChildThreshold B q allowance draw).den ∣
      coarseCommonDenominator 1 q L B (j + (d + 1)) := by
  apply (coarseChildAllowance_grid B q L j allowance draw hB hq hL ha).trans
  refine ⟨q * (L * B * q) ^ d, ?_⟩
  simp only [coarseCommonDenominator, one_mul, pow_add, pow_succ]
  ring

end EditApproximation

end OAI
