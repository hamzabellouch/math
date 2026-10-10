import OAI.NumberTheory.Ostmann.Construction.FullAtomWeightSupport

namespace OAI

/-! # Energy of the actual Fourier weight from its initial modulus window -/

namespace Ostmann

open scoped BigOperators Classical ComplexConjugate SchwartzMap FourierTransform

theorem normalizedFourier_window_square_exp_le (ψ : 𝓢(ℝ, ℂ))
    (X M v lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 ψ ≤ Real.exp K) :
    ‖(if M / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
        normalizedFourierProfile ψ v (M / X)‖ ^ 2 ≤
      Real.exp (-Δ + (C + 2 * K)) := by
  by_cases hm : M / X ∈ Set.Icc lo hi
  · have hMX : X * Real.exp (Δ - C) ≤ M := by
      simpa only [mul_comm] using (le_div_iff₀ hX).mp (hlo.trans hm.1)
    have hM : 0 < M := lt_of_lt_of_le (mul_pos hX (Real.exp_pos _)) hMX
    simp only [hm, ite_true, one_mul]
    rw [normalizedFourierProfile_original ψ X M v hX.ne' hM.ne']
    exact archimedeanLeafFactor_square_exp_le X M v 1 Δ C K ψ
      (by norm_num) (fun u => ((schwartz_profile_bounds ψ).1 u).trans hψ)
      (fun _ => ⟨hM, hMX⟩)
  · simp only [hm, ite_false, zero_mul, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (Real.exp_pos _).le

/-- Every inherited support test is retained; the energy exponent comes solely
from the initial product window and the Fourier transform's Schwartz seminorm. -/
theorem fullAtomFourierWeight_square_exp_le {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (n : ℕ) (x : CopyScheduleAtoms role n → ℕ) (t : FrequencyTree ℤ n) :
    ‖fullAtomTransferWeight role childBound pivotBound ranges
        (fun τ v => (if (scheduleAtomTotal role τ : ℝ) / X ∈ Set.Icc lo hi then (1 : ℂ) else 0) *
          normalizedFourierProfile (𝓕 ψ : 𝓢(ℝ, ℂ)) v ((scheduleAtomTotal role τ : ℝ) / X))
        n x t‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  apply fullAtomTransferWeight_square_exp_le role childBound pivotBound ranges _ Δ (C + 2 * K)
  intro τ v
  exact normalizedFourier_window_square_exp_le (𝓕 ψ) X (scheduleAtomTotal role τ)
    v lo hi Δ C K hX hlo hψ

theorem groupedFullCoprimeFourierWeight_square_exp_le {I V : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (n : ℕ) (words : CopyScheduleAtoms role n → List V)
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi Δ C K : ℝ) (hX : 0 < X)
    (hlo : Real.exp (Δ - C) ≤ lo)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K)
    (t : FrequencyTree ℤ n) (q : V → ℕ) :
    ‖groupedFullCoprimeFourierWeight role n words childBound pivotBound ranges ψ X lo hi t q‖ ^ 2 ≤
      Real.exp (-(2 ^ n : ℕ) * Δ + (2 ^ n : ℕ) * (C + 2 * K)) := by
  rw [groupedFullCoprimeFourierWeight_atom]
  exact fullAtomFourierWeight_square_exp_le role childBound pivotBound ranges
    ψ X lo hi Δ C K hX hlo hψ n _ t

end Ostmann

end OAI
