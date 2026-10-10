import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDetectorPolynomial
import OAI.NumberTheory.Ostmann.ZeroDensity.DensityDyadicPartition

namespace OAI

/-! # Exact dyadic decomposition of the original polynomial alternative -/

namespace Ostmann

open scoped BigOperators Classical

 theorem densityDetector_polynomial_extended (χ : PrimitiveComplexCharacter) (X N : ℕ)
    (Y : ℝ) (hY : 0 < Y) (hN : ⌊Y⌋₊ ≤ N) (β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      densityCharacterPolynomial (Finset.Icc 1 N)
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [densityDetector_polynomial]
  unfold densityCharacterPolynomial
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans hN⟩
  · intro n hn hn'
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hfloor : ⌊Y⌋₊ < n := by
      have hnnot : ¬ n ≤ ⌊Y⌋₊ := fun h => hn' (Finset.mem_Icc.mpr ⟨hn1, h⟩)
      omega
    have hyn : Y < n := (Nat.floor_lt hY.le).mp hfloor
    rw [densityVerticalCoeff, densityPolynomialCoefficient_above X n Y hY hyn.le]
    simp

 theorem densityDetector_polynomial_blocks (χ : PrimitiveComplexCharacter) (X J : ℕ)
    (hX : 1 ≤ X) (Y : ℝ) (hY : 0 < Y) (hcover : ⌊Y⌋₊ ≤ 2 ^ J * X) (β t : ℝ) :
    (∑ n ∈ (Finset.Icc 1 ⌊Y⌋₊).filter (fun n => X < n),
      LSeries.term (densityDetectorCharacterCoefficient χ X) (densityVerticalPoint β t) n *
        densityDetectorWeight (n / Y)) =
      ∑ j ∈ Finset.range J, densityCharacterPolynomial
        (Finset.Ioc (2 ^ j * X) (2 * (2 ^ j * X)))
        (densityVerticalCoeff (densityPolynomialCoefficient X Y) β) χ.character t := by
  rw [densityDetector_polynomial_extended χ X (2 ^ J * X) Y hY hcover]
  unfold densityCharacterPolynomial
  rw [density_dyadic_partition X J hX]
  have hhead : (∑ n ∈ Finset.Icc 1 X,
      densityVerticalCoeff (densityPolynomialCoefficient X Y) β n * χ.character (n : ZMod χ.modulus) *
        realAdditivePhase (-(Real.log n * t))) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [densityVerticalCoeff, densityPolynomialCoefficient_below X n Y (Finset.mem_Icc.mp hn).2]
    simp
  rw [hhead, zero_add]
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  rw [pow_succ]
  ring

end Ostmann

end OAI
