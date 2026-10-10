import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallCorrectionIdentity

namespace OAI

/-! # Full frequency assembly of the original small-kernel term -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate SchwartzMap FourierTransform

private theorem if_sum_zero (p : Prop) [Decidable p] (S : Finset ℕ) (f : ℕ → ℂ) :
    (if p then ∑ d ∈ S, f d else 0) = ∑ d ∈ S, if p then f d else 0 := by
  by_cases hp : p <;> simp [hp]

noncomputable def quadraticGcdSmallTotal (M J : ℝ) (R D K : ℕ) (v w : ℕ → ℂ) : ℂ :=
  ∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
    ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b

theorem quadratic_gcd_small_total_split {M : ℝ} (hM : 0 < M) (J : ℝ)
    {R D : ℕ} (hD : Squarefree D) (ho : Odd D) (K : ℕ) (v w : ℕ → ℂ) :
    let N := quadraticGcdBlockSize R D
    let v' := quadraticGcdBlockCoeff R D v
    let w' := quadraticGcdBlockCoeff R D w
    quadraticGcdSmallTotal M J R D K v w =
      ∑ e ∈ (2 * D).divisors,
        (-(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ) *
          quadraticFullSmallHighCorrection M J e N ((2 * N) ^ 2) K
            (fun _ b => D.Coprime b) v' w' +
        ((Real.sqrt M : ℂ) / 2) *
          quadraticFullSmallMiddleCorrection quadraticSieveWeight M J e N ((2 * N) ^ 2) K
            (quadraticSecondWindow J) (fun _ b => D.Coprime b) v' w') := by
  classical
  dsimp only
  let N := quadraticGcdBlockSize R D
  let v' := quadraticGcdBlockCoeff R D v
  let w' := quadraticGcdBlockCoeff R D w
  let hi := fun (e b : ℕ) => (1 / (Real.sqrt b : ℂ)) *
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      if quadraticSecondUpper (quadraticSmallScale M b) J < (e * d : ℕ) then
        ((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0
  let mi := fun (e b : ℕ) => (1 / (Real.sqrt b : ℂ)) *
    ∑ d ∈ Finset.Icc 1 ((2 * N) ^ 2),
      if quadraticSecondLower (quadraticSmallScale M b) J < (e * d : ℕ) ∧
          (e * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J then
        (((ArithmeticFunction.moebius (e * d) : ℂ) / (e * d : ℕ)) *
          quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
            (quadraticSmallScale M b / (e * d : ℕ)) (quadraticSecondWindow J)) *
          quadraticDivisorBilinear (2 * N) (2 * N) d v' w' b else 0
  let cH := -(∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) * (Real.sqrt M : ℂ)
  let cM := (Real.sqrt M : ℂ) / 2
  have hh (e : ℕ) : (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), hi e b) =
      quadraticFullSmallHighCorrection M J e N ((2 * N) ^ 2) K (fun _ b => D.Coprime b) v' w' := by
    dsimp only [hi]
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [if_sum_zero]
    rw [Finset.sum_comm]
    unfold quadraticFullSmallHighCorrection
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    split_ifs <;> first | tauto | ring
  have hm (e : ℕ) : (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·), mi e b) =
      quadraticFullSmallMiddleCorrection quadraticSieveWeight M J e N ((2 * N) ^ 2) K
        (quadraticSecondWindow J) (fun _ b => D.Coprime b) v' w' := by
    dsimp only [mi]
    simp only [Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    simp_rw [if_sum_zero]
    rw [Finset.sum_comm]
    unfold quadraticFullSmallMiddleCorrection
    apply Finset.sum_congr rfl
    intro d _
    apply Finset.sum_congr rfl
    intro b _
    dsimp only
    split_ifs <;> first | tauto | ring
  have hp (b : ℕ) (_hb : b ∈ (oddSquarefreeRange K).filter (D.Coprime ·)) :
      (∑ z ∈ quadraticGcdPairs (2 * R) D, v z.1 * conj (w z.2) *
        ((jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
          quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b)) =
        ∑ e ∈ (2 * D).divisors, (cH * hi e b + cM * mi e b) := by
    exact quadratic_gcd_small_frequency_split (R := R) (b := b) hM J hD ho v w
  unfold quadraticGcdSmallTotal
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [show (∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      ∑ z ∈ quadraticGcdPairs (2 * R) D, _) =
        ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
          ∑ e ∈ (2 * D).divisors, (cH * hi e b + cM * mi e b) from Finset.sum_congr rfl hp]
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hh, hm]
  rfl

end Ostmann

end OAI
