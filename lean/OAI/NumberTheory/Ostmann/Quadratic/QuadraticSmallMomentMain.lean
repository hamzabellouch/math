import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernelMain
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallMomentError

namespace OAI

/-! # The literal small-kernel moment: original main term and two corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators ComplexConjugate FourierTransform

noncomputable def quadraticSmallPairCorrection (M J : ℝ) (q b : ℕ) : ℂ :=
  let X := quadraticSmallScale M b
  let U := quadraticSecondLower X J
  let V := quadraticSecondUpper X J
  show ℂ from
  -(X : ℂ) * (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)), (ArithmeticFunction.moebius d : ℂ) / d) +
  (X : ℂ) / 2 *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest quadraticSieveWeight))
          (X / d) (quadraticSecondWindow J))

theorem quadratic_small_pair_core (M J : ℝ) (q b : ℕ) :
    quadraticSmallDyadicCore quadraticSieveWeight M b J q b =
      (quadraticSmallScale M b : ℂ) * ((q.totient : ℂ) / q) *
        (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) +
      quadraticSmallPairCorrection M J q b := by
  unfold quadraticSmallDyadicCore quadraticSmallPoissonCore quadraticSmallPairCorrection
  dsimp only
  simp only [quadraticSmallScale]
  ring_nf

noncomputable def quadraticSmallMomentCorrections (M N K : ℕ) (J : ℝ) (v : ℕ → ℂ) : ℂ :=
  ∑ D ∈ Finset.Icc 1 N, ∑ z ∈ quadraticGcdPairs N D,
    v z.1 * conj (v z.2) * ∑ b ∈ (oddSquarefreeRange K).filter (D.Coprime ·),
      (jacobiSym b (quadraticPairKernel z.1 z.2) : ℂ) *
        quadraticSmallPairCorrection M J (2 * (quadraticPairKernel z.1 z.2 * D)) b

theorem quadratic_small_moment_core_decomposition (M N K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticSmallMomentCore M N K J v =
      (∑ D ∈ Finset.Icc 1 N, quadraticSmallTransformedMain M N D K quadraticSieveWeight v) +
        quadraticSmallMomentCorrections M N K J v := by
  unfold quadraticSmallMomentCore quadraticSmallMomentCorrections quadraticSmallTransformedMain
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun x => v z.1 * conj (v z.2) * x)
  apply Finset.sum_congr rfl
  intro b _
  rw [quadratic_small_pair_core]
  ring

theorem quadraticGcdPairs_empty_of_not_odd (N D : ℕ) (hD : ¬ Odd D) :
    quadraticGcdPairs N D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨hz, hg⟩ := Finset.mem_filter.mp hz
  have hs := (Finset.mem_product.mp hz).1
  have ho := (Finset.mem_filter.mp hs).2.1
  apply hD
  rw [← hg]
  exact ho.of_dvd_nat (Nat.gcd_dvd_left z.1 z.2)

theorem quadratic_small_moment_original_main {M : ℕ} (hM : 0 < M)
    (N K : ℕ) (J : ℝ) (v : ℕ → ℂ) :
    quadraticSmallMomentCore M N K J v =
      ((Real.sqrt M : ℂ) / 2 * (∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2))) *
        (∑ D ∈ Finset.Icc 1 N, quadraticSecondMain N D K v) +
          quadraticSmallMomentCorrections M N K J v := by
  rw [quadratic_small_moment_core_decomposition, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro D _
  by_cases hD : Odd D
  · exact quadratic_small_transformed_main (by exact_mod_cast hM) N D K hD quadraticSieveWeight v
  · have he := quadraticGcdPairs_empty_of_not_odd N D hD
    simp only [quadraticSmallTransformedMain, quadraticSecondMain, he, Finset.sum_empty, mul_zero]

end Ostmann

end OAI
