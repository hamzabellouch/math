import OAI.NumberTheory.Ostmann.Construction.WordCharacterRemoval
import OAI.NumberTheory.Ostmann.Arithmetic.SampledTupleAmplitude

namespace OAI

/-! # The initial graph amplitude under the original word and cell laws -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

noncomputable def wordGraphAmplitude {B : Type*} {k m : ℕ}
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (bin : (Fin k → P) → B) (b : B) : ℂ :=
  ∑ x ∈ (wordCharacterEvent μ ν bin b).filter Function.Injective,
    (productPrior (Fin.append (Fin.append μ ν) (Fin.append μ ν)) x : ℂ) *
      sampledTupleAmplitude P hP (wordCopyCharacter k m χ) t ψ X N x

theorem wordGraphAmplitude_eq {B : Type*} {k m : ℕ}
    [Nonempty (Fin ((k + m) + (k + m)))]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (μ : Fin k → P → ℝ) (ν : Fin m → P → ℝ)
    (χ : ∀ p : ℕ, DirichletCharacter ℂ p) (hχ : ∀ p ∈ P, χ p ≠ 1)
    (t : ∀ p : ℕ, ZMod p) (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X)
    (N : ℕ) (hsupp : ∀ u : ℝ, H < |u| → 𝓕 ψ u = 0)
    (bin : (Fin k → P) → B) (b : B)
    (hcut : ∀ x ∈ wordCharacterEvent μ ν bin b,
      H * (∏ i, (x i : ℕ)) ≤ N * X) :
    injectiveWordCharacterMean Subtype.val μ ν χ t ψ X bin b / (Real.sqrt X : ℂ) =
      wordGraphAmplitude P hP μ ν χ t ψ X N bin b := by
  unfold injectiveWordCharacterMean wordGraphAmplitude
  rw [Finset.sum_div]
  apply Finset.sum_congr (by ext x; simp only [Finset.mem_filter])
  intro x hx
  rw [mul_div_assoc]
  congr 1
  simpa only [Function.comp_def] using sampledTupleAmplitude_eq P hP (wordCopyCharacter k m χ)
    (fun i p hp => wordCopyCharacter_ne_one χ p (hχ p hp) i) t ψ X H hX N hsupp x
    (Finset.mem_filter.mp hx).2 (hcut x (Finset.mem_filter.mp hx).1)

theorem initial_amplitude_lower (u v η : ℂ) (X S E : ℝ) (hX : 0 < X)
    (hS : S ≤ u.re) (hE : ‖u - v‖ ≤ E) (hη : v / (Real.sqrt X : ℂ) = η) :
    (S - E) / Real.sqrt X ≤ ‖η‖ := by
  have hu : u.re ≤ ‖u - v‖ + ‖v‖ :=
    (Complex.re_le_norm u).trans (by
      simpa only [sub_add_cancel] using norm_add_le (u - v) v)
  have hlow : S - E ≤ ‖v‖ := by linarith
  rw [← hη, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg X)]
  exact div_le_div_of_nonneg_right hlow (Real.sqrt_pos.mpr hX).le

end Ostmann

end OAI
