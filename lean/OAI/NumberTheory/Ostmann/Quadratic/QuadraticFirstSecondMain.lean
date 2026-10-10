import OAI.NumberTheory.Ostmann.Quadratic.QuadraticFirstSecondKernel
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticTransformedMain

namespace OAI

/-! # The second Poisson core has exactly the original main term and corrections -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSecondCorrection (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) : ℂ :=
  (-𝓕 ρ 0 * (∑ d ∈ q.divisors.filter (fun d : ℕ => (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ)) -
    ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
      ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
      (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) +
    ∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) *
        quadraticLatticeWindow (𝓕 (quadraticFourierSquare ρ a ha)) (X / d) L) / 2

theorem quadratic_second_core_split (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (X U V : ℝ) (L : ℕ) :
    quadraticSecondPoissonCore q ρ a ha X U V L =
      ((X : ℂ) * q.totient / q) *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 +
      quadraticSecondCorrection q ρ a ha X U V L := by
  unfold quadraticSecondPoissonCore quadraticSecondCorrection
  ring

noncomputable def quadraticSecondDyadicCorrection (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (M H J : ℝ) (e q b : ℕ) : ℂ :=
  let X₀ := Real.sqrt ((e : ℝ) * H ^ 2 / (M * b))
  quadraticSecondCorrection q ρ a ha (quadraticSecondScale M e q b)
    (quadraticSecondLower X₀ J) (quadraticSecondUpper X₀ J) (quadraticSecondWindow J)

theorem quadratic_second_dyadic_core_split (ρ : 𝓢(ℝ, ℂ))
    (a : ℝ) (ha : 1 ≤ |a|) (M H J : ℝ) (e q b : ℕ) :
    quadraticSecondDyadicCore ρ a ha M b H J e q b =
      ((quadraticSecondScale M e q b : ℂ) * q.totient / q) *
        ((quadraticFresnelPhase a / (Real.sqrt |a| : ℂ)) *
          ∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) / 2 +
      quadraticSecondDyadicCorrection ρ a ha M H J e q b :=
  quadratic_second_core_split q ρ a ha _ _ _ _

noncomputable def quadraticFirstSecondMainKernel (M D q K : ℕ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
          ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
          (((quadraticSecondScale M e q b : ℂ) * q.totient / q) *
            ((quadraticFresnelPhase (a : ℤ) / (Real.sqrt |((a : ℤ) : ℝ)| : ℂ)) *
              ∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) / 2)

noncomputable def quadraticFirstSecondCorrections (M D q K : ℕ) (H J : ℝ) : ℂ :=
  quadraticGaussMultiplier q * ∑ e ∈ (2 * D).divisors,
    (ArithmeticFunction.moebius e : ℂ) *
      (((M : ℝ) / ((e : ℝ) * Real.sqrt q) : ℝ) : ℂ) *
        ∑ a : quadraticPoissonSigns, ∑ b ∈ oddSquarefreeRange K,
          ((jacobiSym ((e : ℤ) * a) q : ℂ) * (jacobiSym b q : ℂ)) *
            quadraticSecondDyadicCorrection quadraticSieveWeight (a : ℤ)
              (quadraticPoissonSigns_abs a.property) M H J e q b

theorem quadratic_first_second_kernel_split (M D q K : ℕ) (H J : ℝ) :
    quadraticFirstSecondKernel M D q K H J =
      quadraticFirstSecondMainKernel M D q K + quadraticFirstSecondCorrections M D q K H J := by
  unfold quadraticFirstSecondKernel quadraticFirstSecondMainKernel quadraticFirstSecondCorrections
    quadraticSignedSecondCore
  simp_rw [quadratic_second_dyadic_core_split, mul_add, Finset.sum_add_distrib]
  simp only [mul_add, Finset.sum_add_distrib]

theorem quadratic_first_second_main_kernel (M D q K : ℕ) :
    quadraticFirstSecondMainKernel M D q K =
      ((∫ x in Ioi (0 : ℝ), quadraticSieveWeight (x ^ 2)) / 2) *
      ((q.totient : ℂ) / q) * ∑ b ∈ oddSquarefreeRange K,
        (jacobiSym b q : ℂ) * quadraticDualMainCoefficient M D q b := by
  have hs (f : ℤ → ℂ) : (∑ a : quadraticPoissonSigns, f a) =
      ∑ a ∈ ({1, -1, 2, -2} : Finset ℤ), f a := Finset.sum_coe_sort quadraticPoissonSigns f
  have hr (F : ℕ → quadraticPoissonSigns → ℕ → ℂ) :
      (∑ e ∈ (2 * D).divisors, ∑ a : quadraticPoissonSigns,
        ∑ b ∈ oddSquarefreeRange K, F e a b) =
      ∑ b ∈ oddSquarefreeRange K, ∑ e ∈ (2 * D).divisors,
        ∑ a : quadraticPoissonSigns, F e a b := by
    calc
      _ = ∑ e ∈ (2 * D).divisors, ∑ b ∈ oddSquarefreeRange K,
          ∑ a : quadraticPoissonSigns, F e a b := by
        apply Finset.sum_congr rfl
        intro e _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  unfold quadraticFirstSecondMainKernel quadraticDualMainCoefficient
  simp_rw [← hs]
  simp only [Finset.mul_sum]
  rw [hr]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  push_cast
  ring

end Ostmann

end OAI
