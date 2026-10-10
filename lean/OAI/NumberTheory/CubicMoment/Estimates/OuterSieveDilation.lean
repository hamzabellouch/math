import OAI.NumberTheory.CubicMoment.Estimates.OuterSievePowers

namespace OAI

/-! Absorb fixed dyadic dilation and lattice counting into one constant
before minimizing the two outer-sieve orientations. -/
noncomputable section
namespace CubicFirstMoment

lemma sieve_doubled_bracket {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N) :
    2*M+N+(2*M*N)^(2/3:ℝ) ≤ 2*(M+N+(M*N)^(2/3:ℝ)) := by
  have htwo : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (2/3:ℝ) ≤ 1)
  have hp : (2*M*N)^(2/3:ℝ) ≤ 2*(M*N)^(2/3:ℝ) := by
    rw [mul_assoc,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (mul_nonneg hM hN)]
    exact mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (mul_nonneg hM hN) _)
  linarith

lemma sieve_doubled_term {M N B A K ε : ℝ} (hM : 0 ≤ M) (hMB : M ≤ B)
    (hN : 0 ≤ N) (hA : 0 ≤ A) (_hK : 0 ≤ K) (hKA : K ≤ 36*A) (hε : 0 ≤ ε) :
    K*(2*M*N)^ε*(2*M+N+(2*M*N)^(2/3:ℝ)) ≤
      (72*(2*B*N)^ε)*(A*(M+N+(M*N)^(2/3:ℝ))) := by
  have hB0 : 0 ≤ B := hM.trans hMB
  have hbase : 0 ≤ 2*M*N := mul_nonneg (mul_nonneg (by norm_num) hM) hN
  have hp : (2*M*N)^ε ≤ (2*B*N)^ε := Real.rpow_le_rpow hbase
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB (by norm_num)) hN) hε
  have hKp := mul_le_mul hKA hp (Real.rpow_nonneg hbase ε) (by positivity : 0 ≤ 36*A)
  have hbr := sieve_doubled_bracket hM hN
  calc
    _ ≤ (36*A)*(2*B*N)^ε*(2*(M+N+(M*N)^(2/3:ℝ))) :=
      mul_le_mul hKp hbr (by positivity) (by positivity)
    _ = _ := by ring

lemma outer_dyadic_sieve_min {P Q B N S T ε : ℝ}
    (hP : 0 ≤ P) (hPB : P ≤ B) (hQ : 0 ≤ Q) (hQB : Q ≤ B)
    (hN : 0 ≤ N) (hS : 0 ≤ S) (hSP : S ≤ 36*P)
    (hT : 0 ≤ T) (hTQ : T ≤ 36*Q) (hε : 0 ≤ ε) :
    min (T*(2*P*N)^ε*(2*P+N+(2*P*N)^(2/3:ℝ)))
      (S*(2*Q*N)^ε*(2*Q+N+(2*Q*N)^(2/3:ℝ))) ≤
      (72*(2*B*N)^ε)*
        min (Q*(P+N+(P*N)^(2/3:ℝ))) (P*(Q+N+(Q*N)^(2/3:ℝ))) := by
  have hB0 : 0 ≤ B := hP.trans hPB
  rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 72*(2*B*N)^ε)]
  exact min_le_min (sieve_doubled_term hP hPB hN hQ hT hTQ hε)
    (sieve_doubled_term hQ hQB hN hP hS hSP hε)

end CubicFirstMoment

end

end OAI
