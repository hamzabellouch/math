import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.UnitTorusCoefficients

namespace OAI

/-! # Polynomial coefficient fields for the exact scalar linearization -/

open scoped ComplexConjugate

namespace DefocusingNLS

noncomputable def expandingConstant (a k L : ℝ) (c : ℂ) : FourierL2 :=
  lp.single 2 0 ((expandingSobolevWeight a k L 0 : ℂ) * c)

theorem expandingConstant_coefficient (a k L : ℝ) (hL : 1 ≤ L) (c : ℂ) (n : frequencyLattice) :
    expandingFourierCoefficient a k L (expandingConstant a k L c) n = if n = 0 then c else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    simp only [ite_true]
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k L hL 0).ne')
    rw [weight_mul_expandingFourierCoefficient a k L hL]
    simp [expandingConstant]
  · simp [expandingConstant, expandingFourierCoefficient, lp.single_apply, hn]

theorem expandingConstant_function (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (c : ℂ) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (expandingConstant a k L c) x = c := by
  classical
  have hz : frequencyCoordinates (0 : frequencyLattice) = 0 := frequencyCoordinatesEquiv.map_zero
  rw [expandingTorusFunction_apply a k L ha ha1 hk hL]
  simp only [expandingConstant_coefficient a k L hL]
  rw [tsum_eq_single 0]
  · simp [torusCharacter, hz]
  · intro n hn
    simp [hn]

noncomputable def expandingPower (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (q : FourierL2) : ℕ → FourierL2
  | 0 => expandingConstant a k L 1
  | n + 1 => expandingProduct a k L ha ha1 hk hL q (expandingPower a k L ha ha1 hk hL q n)

theorem expandingPower_function (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L)
    (q : FourierL2) (n : ℕ) (x : SchrodingerTorus) :
    expandingTorusFunction a k L (expandingPower a k L ha ha1 hk hL q n) x =
      (expandingTorusFunction a k L q x) ^ n := by
  induction n with
  | zero => simp only [expandingPower, expandingConstant_function a k L ha ha1 hk hL, pow_zero]
  | succ n ih =>
    simp only [expandingPower, expandingTorusFunction_product a k L ha ha1 hk hL,
      ContinuousMap.mul_apply, ih, pow_succ]
    ring

theorem expandingTorusFunction_injective (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) :
    Function.Injective (expandingTorusFunction a k L) := by
  intro f g hfg
  ext n
  have he := expandingFourierCoefficient_eq_of_torus_eq a k L ha ha1 hk hL f g
    (fun x => congrArg (fun F : C(SchrodingerTorus, ℂ) => F (euclideanToTorus x)) hfg) n
  rw [← weight_mul_expandingFourierCoefficient a k L hL f n,
    ← weight_mul_expandingFourierCoefficient a k L hL g n, he]

noncomputable def expandingCircularCoefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q : FourierL2) : FourierL2 :=
  ((m + 1 : ℕ) : ℂ) • expandingProduct a k L ha ha1 hk hL
    (expandingPower a k L ha ha1 hk hL q m)
    (expandingPower a k L ha ha1 hk hL (fourierConjugate q) m)

noncomputable def expandingAnticircularCoefficient (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q : FourierL2) : FourierL2 :=
  (m : ℂ) • expandingProduct a k L ha ha1 hk hL
    (expandingPower a k L ha ha1 hk hL q (m + 1))
    (expandingPower a k L ha ha1 hk hL (fourierConjugate q) (m - 1))

theorem expandingOddPower_derivative_algebra (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (m : ℕ) (q f : FourierL2) :
    fderiv ℝ (expandingOddPower a k L ha ha1 hk hL m) q f =
      expandingProduct a k L ha ha1 hk hL
        (expandingCircularCoefficient a k L ha ha1 hk hL m q) f +
      expandingProduct a k L ha ha1 hk hL
        (expandingAnticircularCoefficient a k L ha ha1 hk hL m q) (fourierConjugate f) := by
  apply expandingTorusFunction_injective a k L ha ha1 hk hL
  ext x
  have hadd (u v : FourierL2) : expandingTorusFunction a k L (u + v) x =
      expandingTorusFunction a k L u x + expandingTorusFunction a k L v x := by
    simp only [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_add]
  have hsmul (c : ℂ) (u : FourierL2) : expandingTorusFunction a k L (c • u) x =
      c * expandingTorusFunction a k L u x := by
    simp only [expandingTorusFunction_eq_evaluation a k L ha ha1 hk hL, map_smul, smul_eq_mul]
  rw [expandingOddPower_fderiv_pointwise_explicit]
  simp only [expandingCircularCoefficient, expandingAnticircularCoefficient, hadd, hsmul,
    expandingTorusFunction_product a k L ha ha1 hk hL, ContinuousMap.mul_apply,
    expandingPower_function a k L ha ha1 hk hL,
    expandingTorusFunction_conjugate a k L ha ha1 hk hL, starRingEnd_apply]
  ring

end DefocusingNLS

end OAI
