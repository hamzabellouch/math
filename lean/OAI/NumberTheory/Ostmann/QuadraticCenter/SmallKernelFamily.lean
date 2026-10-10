import OAI.NumberTheory.Ostmann.QuadraticCenter.FullCoefficientMass

namespace OAI

/-! # The fixed family with the scale needed for the small-kernel estimate -/

namespace Ostmann

open Filter
open scoped BigOperators SchwartzMap

noncomputable def smallKernelParameters (T : ℝ) (L : ℕ) : Finset QuadraticFamilyIndex :=
  (quadraticFamilyParameters T L).filter (fun i =>
    i.2.2.1 = 1 ∧ (L : ℝ) ^ 6 ≤ quadraticGridScale (Real.exp (-200 * T)) i.2.2.2)

theorem smallKernelParameters_subset (T : ℝ) (L : ℕ) :
    smallKernelParameters T L ⊆ quadraticFamilyParameters T L := Finset.filter_subset _ _

theorem eventual_small_kernel_family_covers (H : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hH : 0 ≤ H) (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (D : ∀ p : ℕ, Finset (ZMod p)) (M h₀ : ℕ) (θ R : ℝ),
      (Q.card : ℝ) ≤ T → (∀ p ∈ Q, 1000000 ≤ p) →
      (Q.toList.prod : ℝ) ≤ Real.exp T → Odd M → h₀ < Q.toList.prod →
      0 ≤ θ → θ ≤ 1 → 1 ≤ R → R ≤ Real.exp (14 * T) →
      (Q.toList.prod : ℝ) ^ 6 + Real.exp (-200 * T) ≤ R →
      ∃ i ∈ smallKernelParameters T Q.toList.prod, ∀ s : ℕ,
        1 ≤ s → (s : ℝ) ≤ Real.exp (14 * T) →
        ‖arithmeticQuadraticCoefficient Q hQ D Φ R 1 M h₀ θ s -
          fixedQuadraticCoefficient T Q hQ D Φ i s‖ ≤ Real.exp (-127 * T) := by
  filter_upwards [eventual_fixed_quadratic_family_covers H Φ hH hΦ,
    eventually_ge_atTop (0 : ℝ)] with T hc hT
  intro Q hQ D M h₀ θ R hcard hlarge hL hM hh₀ hθ0 hθ1 hR hRU hmargin
  obtain ⟨i, hi, hiP, hiR, he⟩ := hc Q hQ D M h₀ 1 θ R hcard hlarge hL hM hh₀
    (by decide) (by simpa using Real.one_le_exp_iff.mpr (show 0 ≤ 7 * T by positivity))
    hθ0 hθ1 hR hRU
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, hiP, ?_⟩, he⟩
  have hr := (le_abs_self (R - quadraticGridScale (Real.exp (-200 * T)) i.2.2.2)).trans hiR
  linarith

theorem eventual_small_kernel_family_norm (C₀ H ε : ℝ) (Φ : 𝓢(ℝ, ℂ))
    (hC₀ : 0 ≤ C₀) (hH : 0 ≤ H) (hε : 0 < ε)
    (hΦ : ∀ x : ℝ, H < x → Φ x = 0) :
    ∀ᶠ T : ℝ in atTop, ∀ (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
      (M : ℕ) (S : Finset ℕ) (u : ℝ),
      T ^ (9999999 / 10000000 : ℝ) / 1000 ≤ (Q.card : ℝ) →
      (∀ p ∈ Q, 1000000 ≤ p) → (M : ℝ) ≤ Real.exp (C₀ * T) →
      (∀ s ∈ S, Squarefree s ∧ s ≤ M ∧ s ≤ Q.toList.prod ^ 4) →
      0 ≤ u → u ≤ 2 * T ^ (1 / 1000000 : ℝ) →
      ∀ (D : ∀ p : ℕ, Finset (ZMod p)) (i : QuadraticFamilyIndex),
      i ∈ smallKernelParameters T Q.toList.prod →
      Real.sqrt (∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) *
        ‖fixedQuadraticCoefficient T Q hQ D Φ i s‖ ^ 2) ≤
        Real.exp ((101 / 1000 + ε) * Q.card) := by
  filter_upwards [eventual_full_small_kernel_norm C₀ H ε Φ hC₀ hH hε hΦ] with T hn
  intro Q hQ M S u hK hlarge hM hS hu huU D i hi
  have hh := (Finset.mem_filter.mp hi).2
  simp only [fixedQuadraticCoefficient, arithmeticQuadraticCoefficient, hh.1]
  exact hn Q hQ M S u hK hlarge hM hS hu huU D _ _ _ _ _ hh.2
    (fun U _ => quadraticSymbolCoefficient_norm_le _ U)
    (fun V _ => quadraticDivisorSymbol_norm_le _ V)

end Ostmann

end OAI
