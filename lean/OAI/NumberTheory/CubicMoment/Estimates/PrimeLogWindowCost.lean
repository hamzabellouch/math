import OAI.NumberTheory.CubicMoment.Estimates.PrimeLogWindow

namespace OAI

/-! Polynomial finite-seminorm cost of the actual narrowing cutoff. -/
noncomputable section
open scoped ContDiff SchwartzMap BigOperators
namespace CubicFirstMoment

lemma primeLogWindow_seminorm_bound (k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      SchwartzMap.seminorm ℝ k n (primeLogWindowSchwartz J (by linarith)) ≤ C*J^n := by
  obtain ⟨C,hC,hder⟩ := primeLogWindow_derivative_bound n
  refine ⟨2^k*C,by positivity,?_⟩
  intro J hJ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2
  · have hb := hder J u hJ
    change ‖u‖^k*‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ _
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 2^k*(C*J^n) := mul_le_mul
        (pow_le_pow_left₀ (abs_nonneg _) hu k) hb (_root_.norm_nonneg _) (by positivity)
      _ = _ := by ring
  · have hz : iteratedFDeriv ℝ n (primeLogWindow J) u=0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := primeLogWindow J) n hn
      exact hu (primeLogWindow_support_two hJ hs)
    change ‖u‖^k*‖iteratedFDeriv ℝ n (primeLogWindow J) u‖ ≤ _
    rw [hz,norm_zero,mul_zero]
    positivity

theorem primeLogWindow_finite_cost (I : Finset (ℕ × ℕ)) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧ ∀ J : ℝ, (hJ : 1 ≤ J) →
      (I.sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2))
        (primeLogWindowSchwartz J (by linarith)) ≤ K*J^d := by
  classical
  choose C hC hb using fun m : ℕ × ℕ => primeLogWindow_seminorm_bound m.1 m.2
  let d := I.sup Prod.snd
  let K := 1+∑ m ∈ I, C m
  have hK : 0 < K := by
    have hh := Finset.sum_nonneg (fun m (_ : m ∈ I) => hC m)
    dsimp [K]
    linarith
  refine ⟨d,K,hK,?_⟩
  intro J hJ
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro m hm
  have hn : m.2 ≤ d := Finset.le_sup (f := Prod.snd) hm
  have hmK : C m ≤ K := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ I) => hC j) hm
    dsimp [K]
    linarith
  exact (hb m J hJ).trans
    (mul_le_mul hmK (pow_le_pow_right₀ hJ hn) (by positivity) hK.le)

end CubicFirstMoment

end

end OAI
