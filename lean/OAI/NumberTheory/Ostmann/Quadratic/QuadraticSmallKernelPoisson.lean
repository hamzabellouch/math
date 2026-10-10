import OAI.NumberTheory.Ostmann.Quadratic.QuadraticPositiveCoprime
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSquareCompose

namespace OAI

/-! # The actual small-squarefree-kernel Poisson formula -/

namespace Ostmann

open MeasureTheory Set
open scoped Classical BigOperators SchwartzMap FourierTransform

noncomputable def quadraticSmallSquareTest (ρ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  quadraticSquareCompose ρ 1 (by norm_num)

theorem quadraticSmallSquareTest_apply (ρ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    quadraticSmallSquareTest ρ x = ρ (x ^ 2) := by
  simp only [quadraticSmallSquareTest, quadraticSquareCompose_apply, one_mul]

theorem quadraticSmallSquareTest_even (ρ : 𝓢(ℝ, ℂ)) :
    Function.Even (quadraticSmallSquareTest ρ) :=
  quadraticSquareCompose_even ρ 1 _

theorem quadraticSmallSquareTest_fourier_zero (ρ : 𝓢(ℝ, ℂ)) :
    𝓕 (quadraticSmallSquareTest ρ) 0 = 2 * ∫ x in Ioi (0 : ℝ), ρ (x ^ 2) := by
  let ψ := quadraticSmallSquareTest ρ
  have heq : (∫ x in Iic (0 : ℝ), ψ x) = ∫ x in Ioi (0 : ℝ), ψ x := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), ψ (-x) := by
        simpa only [neg_zero] using (integral_comp_neg_Ioi 0 ψ).symm
      _ = _ := setIntegral_congr_fun measurableSet_Ioi
        (fun x _ => quadraticSmallSquareTest_even ρ x)
  rw [quadratic_fourier_phase_integral]
  simp only [mul_zero, neg_zero, realAdditivePhase_zero, one_mul]
  change (∫ x : ℝ, ψ x) = _
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi ψ.integrable,
    compl_Ioi, heq]
  simp only [ψ, quadraticSmallSquareTest_apply]
  ring

noncomputable def quadraticSmallPoissonCore (q : ℕ) (ρ : 𝓢(ℝ, ℂ))
    (X U V : ℝ) (L : ℕ) : ℂ :=
  (X : ℂ) * ((q.totient : ℂ) / q) * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) -
  (X : ℂ) * (∫ x in Ioi (0 : ℝ), ρ (x ^ 2)) *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) / d) +
  (X : ℂ) / 2 *
    (∑ d ∈ q.divisors.filter (fun d : ℕ => U < (d : ℝ) ∧ (d : ℝ) ≤ V),
      ((ArithmeticFunction.moebius d : ℂ) / d) *
        quadraticLatticeWindow (𝓕 (quadraticSmallSquareTest ρ)) (X / d) L)

theorem quadraticSmallPoissonCore_eq (q : ℕ) (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0)
    (X U V : ℝ) (L : ℕ) :
    quadraticSmallPoissonCore q ρ X U V L =
      quadraticPoissonCore q (quadraticSmallSquareTest ρ) X U V L / 2 := by
  have hzero : quadraticSmallSquareTest ρ 0 = 0 := by
    simpa only [quadraticSmallSquareTest_apply, zero_pow (by decide : 2 ≠ 0)] using hρ
  have hsum (F : Finset ℕ) (g : ℕ → ℂ) :
      (∑ d ∈ F, (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ) * g d) =
      (X : ℂ) * ∑ d ∈ F, ((ArithmeticFunction.moebius d : ℂ) / d) * g d := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hlarge : (∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
      (ArithmeticFunction.moebius d : ℂ) * ((X / d : ℝ) : ℂ)) =
      (X : ℂ) * ∑ d ∈ q.divisors.filter (fun d : ℕ => V < (d : ℝ)),
        (ArithmeticFunction.moebius d : ℂ) / d := by
    simpa only [mul_one] using hsum (q.divisors.filter (fun d : ℕ => V < (d : ℝ))) (fun _ => 1)
  unfold quadraticSmallPoissonCore quadraticPoissonCore
  rw [hzero, quadraticSmallSquareTest_fourier_zero, hlarge, hsum]
  ring

theorem quadratic_small_kernel_poisson (ρ : 𝓢(ℝ, ℂ)) (hρ : ρ 0 = 0) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, [NeZero q] → q ≠ 1 →
      ∀ X U V J : ℝ, 0 < X → 0 < U → 0 < V → 1 ≤ J →
      U * J ≤ X → X * J ≤ V → ∀ L : ℕ, (V / X) ^ 2 ≤ (L : ℝ) + 1 →
      ‖(∑' n : ℕ+, (1 : DirichletCharacter ℂ q) (n : ZMod q) *
        ρ (((n : ℝ) / X) ^ 2)) - quadraticSmallPoissonCore q ρ X U V L‖ ≤
          C * X / J ^ A := by
  obtain ⟨C, hC, hc⟩ := quadratic_uniform_positive_poisson
    (quadraticSmallSquareTest ρ) (quadraticSmallSquareTest_even ρ) A
  refine ⟨C, hC, ?_⟩
  intro q _ hq X U V J hX hU hV hJ hUJ hJV L hL
  simpa only [quadraticSmallPoissonCore_eq q ρ hρ X U V L,
    quadraticSmallSquareTest_apply] using hc q hq X U V J hX hU hV hJ hUJ hJV L hL

end Ostmann

end OAI
