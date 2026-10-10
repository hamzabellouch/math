import OAI.NumberTheory.JointDickman.Counting.CountingParameterVariation

namespace OAI

/-! # A uniform bound for the actual counting prime kernel -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem countingPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (D : (Fin 4 →₀ ℕ) → ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T σ : ℝ),
      1 ≤ T → Real.log T ≤ (B : ℝ)/10 → |σ| ≤ 3 →
      ∀ x y, |countingPrimeKernel P m B j c D T σ x y| ≤ K := by
  obtain ⟨K,hK,hbound⟩ := weightedPolynomialPrimeKernel_bounded hM hMP P m hm c hc D
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  refine ⟨K,hK,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 30] with B hb hB
  intro j T σ hT hlog hσ x y
  let S := dyadicBoxIndices (dyadicBoxLower B T) (dyadicBoxUpper B T)
  have hS : ∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*Real.log 2)/T) := by
    intro k hk
    exact (((dyadic_scale_window hB hT hlog).2.1 k hk).2).1
  let r := fun k : ℤ => amplificationBump (Real.log (Real.exp ((k : ℝ)*Real.log 2)/T)/B)
  have hr : ∀ k ∈ S, |r k| ≤ 1 := by
    intro k _
    rw [abs_of_nonneg (amplificationBump_bounds _).1]
    exact (amplificationBump_bounds _).2
  exact hb j T S hS (fun _ => σ) (fun _ _ => hσ) r hr x y

end JointDickman

end OAI
