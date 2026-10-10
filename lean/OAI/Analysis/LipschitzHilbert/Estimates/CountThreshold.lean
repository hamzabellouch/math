import OAI.Analysis.LipschitzHilbert.Estimates.PopularTopCountPowers

namespace OAI

/-! Convert the proved weak square tail and total-area budget into the
manuscript's polynomial count cutoff, with no top-cardinality loss. -/

noncomputable section
namespace LipschitzHilbert

theorem weak_two_polynomial_threshold (C L a s H N F S : ℝ)
    (hC : 0 ≤ C) (hL : 1 ≤ L) (hCL : C ≤ L) (hN : 0 < N)
    (hF : 0 ≤ F) (hS : 0 ≤ S) (harea : S ≤ L^s*N^2*F) :
    (C*L^a*Real.sqrt S)^2/(N*L^(a+(s+H)/2+1))^2 ≤ L^(-H)*F := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let b := a+(s+H)/2+1
  have hden : 0 < (N*L^b)^2 := by positivity
  change (C*L^a*Real.sqrt S)^2/(N*L^b)^2 ≤ _
  apply (div_le_iff₀ hden).mpr
  have hCa : C^2 ≤ L^2 := pow_le_pow_left₀ hC hCL 2
  have ha2 : (L^a)^2 = L^(2*a) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    congr 1
    ring
  have hb2 : (L^b)^2 = L^(2*b) := by
    rw [← Real.rpow_mul_natCast hL0.le]
    congr 1
    ring
  have hpower : L^2*L^(2*a)*L^s = L^(-H)*L^(2*b) := by
    rw [← Real.rpow_two L, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
    congr 1
    dsimp [b]
    ring
  rw [mul_pow, mul_pow, Real.sq_sqrt hS, ha2, mul_pow, hb2]
  calc
    C^2*L^(2*a)*S ≤ C^2*L^(2*a)*(L^s*N^2*F) :=
      mul_le_mul_of_nonneg_left harea (by positivity)
    _ ≤ L^2*L^(2*a)*(L^s*N^2*F) := by gcongr
    _ = (L^(-H)*F)*(N^2*L^(2*b)) := by
      calc
        _ = (L^2*L^(2*a)*L^s)*(N^2*F) := by ring
        _ = _ := by rw [hpower]; ring

end LipschitzHilbert

end

end OAI
