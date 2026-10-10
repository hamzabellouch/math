import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPolynomialMoment

namespace OAI

/-! # Quantitative moments of both circular coefficients -/

namespace DefocusingNLS

attribute [local irreducible] expandingPower expandingProduct expandingFourierCoefficient
  expandingCircularCoefficient expandingAnticircularCoefficient fourierConjugate

variable (a k L : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (N m : ℕ)

 theorem expandingCircular_moment (q : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q))) :
    let M := ∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingCircularCoefficient a k L ha ha1 hk hL m q))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingCircularCoefficient a k L ha ha1 hk hL m q)) n) ≤
      (m + 1 : ℕ) * (M ^ m * M ^ m) := by
  intro M
  have hconj := expandingConjugate_moment a k L N q hq
  have hp := expandingPower_moment a k L ha ha1 hk hL N q hq m
  have hp' := expandingPower_moment a k L ha ha1 hk hL N (fourierConjugate q) hconj.1 m
  rw [hconj.2] at hp'
  have hprod := expandingProduct_moment a k L ha ha1 hk hL N
    (expandingPower a k L ha ha1 hk hL q m)
    (expandingPower a k L ha ha1 hk hL (fourierConjugate q) m) hp.1 hp'.1
  have hc := expandingScalar_moment a k L N ((m + 1 : ℕ) : ℂ)
    (expandingProduct a k L ha ha1 hk hL
      (expandingPower a k L ha ha1 hk hL q m)
      (expandingPower a k L ha ha1 hk hL (fourierConjugate q) m)) hprod.1
  rw [expandingCircularCoefficient]
  refine ⟨hc.1, ?_⟩
  rw [hc.2]
  have hM : 0 ≤ M := tsum_nonneg (fun n => mul_nonneg
    (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _))
  calc
    _ ≤ ‖((m + 1 : ℕ) : ℂ)‖ * (M ^ m * M ^ m) := by
      apply mul_le_mul_of_nonneg_left (hprod.2.trans ?_) (norm_nonneg _)
      exact mul_le_mul hp.2 hp'.2
        (tsum_nonneg (fun n => mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)))
        (pow_nonneg hM m)
    _ = _ := by rw [Complex.norm_natCast]

 theorem expandingAnticircular_moment (q : FourierL2)
    (hq : Summable (latticeMomentMass L N (expandingFourierCoefficient a k L q))) :
    let M := ∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L q) n
    Summable (latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingAnticircularCoefficient a k L ha ha1 hk hL m q))) ∧
    (∑' n, latticeMomentMass L N (expandingFourierCoefficient a k L
      (expandingAnticircularCoefficient a k L ha ha1 hk hL m q)) n) ≤
      (m : ℝ) * (M ^ (m + 1) * M ^ (m - 1)) := by
  intro M
  have hconj := expandingConjugate_moment a k L N q hq
  have hp := expandingPower_moment a k L ha ha1 hk hL N q hq (m + 1)
  have hp' := expandingPower_moment a k L ha ha1 hk hL N (fourierConjugate q) hconj.1 (m - 1)
  rw [hconj.2] at hp'
  have hprod := expandingProduct_moment a k L ha ha1 hk hL N
    (expandingPower a k L ha ha1 hk hL q (m + 1))
    (expandingPower a k L ha ha1 hk hL (fourierConjugate q) (m - 1)) hp.1 hp'.1
  have hc := expandingScalar_moment a k L N (m : ℂ)
    (expandingProduct a k L ha ha1 hk hL
      (expandingPower a k L ha ha1 hk hL q (m + 1))
      (expandingPower a k L ha ha1 hk hL (fourierConjugate q) (m - 1))) hprod.1
  rw [expandingAnticircularCoefficient]
  refine ⟨hc.1, ?_⟩
  rw [hc.2]
  have hM : 0 ≤ M := tsum_nonneg (fun n => mul_nonneg
    (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _))
  calc
    _ ≤ ‖(m : ℂ)‖ * (M ^ (m + 1) * M ^ (m - 1)) := by
      apply mul_le_mul_of_nonneg_left (hprod.2.trans ?_) (norm_nonneg _)
      exact mul_le_mul hp.2 hp'.2
        (tsum_nonneg (fun n => mul_nonneg (le_trans zero_le_one (latticeMomentWeight_one_le L hL N n)) (norm_nonneg _)))
        (pow_nonneg hM (m + 1))
    _ = _ := by rw [Complex.norm_natCast]

end DefocusingNLS

end OAI
