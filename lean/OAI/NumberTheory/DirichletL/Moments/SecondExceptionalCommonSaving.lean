import OAI.NumberTheory.DirichletL.Moments.SecondExceptionalPhysicalSaving

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentSecondExceptionalCommonSaving
open CenteredMomentSecondExceptionalPhysicalSaving
lemma common_weight_bound (Z c d θ B ε δ r:ℝ)(hZ:1<Z)(hc:1≤c)(hd:1≤d)
    (hθ:0≤θ)(hC:c≤Z^B)(hD:d≤Z^B):
    Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*(c*d)^θ*
      Z^(-(Real.logb Z c+Real.logb Z d)/3)≤
        Z^(2*ε+δ+2*B*θ-2*max r 0/3):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hcd:0≤c*d:=mul_nonneg (zero_le_one.trans hc) (zero_le_one.trans hd)
  have hpow:(c*d)^θ≤Z^(2*B*θ):=by
    calc
      _≤(Z^B*Z^B)^θ:=Real.rpow_le_rpow hcd
        (mul_le_mul hC hD (zero_le_one.trans hd) (Real.rpow_nonneg hz.le _)) hθ
      _=Z^(2*B*θ):=by
        rw [←Real.rpow_add hz,←Real.rpow_mul hz.le]
        congr 1;ring
  have hl:=column_cap_ledger (Real.logb Z c) (Real.logb Z d) r
    (Real.logb_nonneg hZ hc) (Real.logb_nonneg hZ hd)
  calc
    _≤Z^(2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)*Z^(2*B*θ)*
      Z^(-(Real.logb Z c+Real.logb Z d)/3):=by gcongr
    _=Z^((2*ε+δ-max (r-min (Real.logb Z c) (Real.logb Z d)) 0)+2*B*θ-
      (Real.logb Z c+Real.logb Z d)/3):=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz]
      congr 1;ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
end SevenEighths.CenteredMomentSecondExceptionalCommonSaving

end

end OAI
