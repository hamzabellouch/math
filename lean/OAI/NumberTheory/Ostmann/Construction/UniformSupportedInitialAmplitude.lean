import OAI.NumberTheory.Ostmann.Construction.InitialAmplitudeErrorBudget
import OAI.NumberTheory.Ostmann.Construction.SupportedHalfInitialAmplitude

namespace OAI

/-! # A uniform exponential lower bound for the actual mixed initial amplitude -/
namespace Ostmann
open Filter
open scoped Classical BigOperators SchwartzMap FourierTransform

/-- The cell count affects the threshold but not the final exponential rate.
All product restrictions are imposed only on the live original prior. -/
theorem uniform_supported_initial_amplitude (r : ℕ) (z A B Bs a c δ : ℝ)
    (hz : 1 ≤ z) (ha : 0 < a) (hc : 0 < c) (hδ : 0 < δ)
    (hBs : 2 * (A + B + 2 * Real.log 4 +
      (4 * (Real.log 2 + 2) + 2 * Real.log 2 + 4) + 3) ≤ Bs)
    (ψ : 𝓢(ℝ, ℂ)) (T : ℝ)
    (hψ : ∀ x, 0 ≤ (ψ x).re) (hsupp : ∀ t : ℝ, T < |t| → 𝓕 ψ t = 0) :
    ∀ᶠ m : ℕ in atTop, ∀ (L Y X Δ R : ℝ),
      0 < L → L ≤ m → (m : ℝ) ≤ z * L →
      0 < Y → Y ≤ Real.exp L → 0 < X → 0 < R →
      (Bs + 8 * Real.log z) * m ≤ Δ →
      ∀ (P : Finset ℕ) [∀ q : P, NeZero (q : ℕ)] (_hP : ∀ q ∈ P, q.Prime),
      ∀ (S : (q : P) → Finset (ZMod (q : ℕ))) (favorable : P → Bool)
        (ν : Fin ((m + r) + 1) → P → ℝ) (C : Fin ((m + r) + 1) → ℝ),
      (∀ i q, 0 ≤ ν i q) → (∀ i, 0 ≤ C i) →
      (∀ i (q : P), (q : ℝ) * ν i q ≤ C i) →
      (∏ i, Fin.append C C i) * L ^ (2 * m) ≤ Real.exp (A * m) →
      (∑ p : P, (p : ℝ)⁻¹) ≤ B * m →
      ∀ (w : (Fin (m + r) → P) → ℝ) (E : Finset ℤ)
        (balanced : Finset (Fin (m + r) → P)),
      (∀ x, 0 ≤ w x) → (∀ x, w x ≤ 1) →
      Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
        ∑ x ∈ balanced, productPrior (Fin.tail ν) x * w x →
      (∀ x ∈ balanced, ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S (x i)) ∧
        residueDensity (S (x i)) ≤ 2 / 3) →
      a * Real.sqrt X / Y ^ 3 ≤ (E.card : ℝ) →
      (∀ e ∈ E, c ≤ (ψ ((e : ℝ) / X)).re) →
      (∀ e ∈ E, ∀ q : P, (e : ZMod (q : ℕ)) ∈ S q) →
      (E.card : ℝ) * δ ≤ ∑ e ∈ E,
        (∑ q : P, (ν 0 q : ℂ) * primePhysicalTest (S q) true (favorable q)
          (e : ZMod (q : ℕ))).re →
      (∀ i (q : P), ν i q ≠ 0 → T * R < (q : ℝ)) →
      ∀ N : ℕ,
      let W := doubledHalfWeight (fun y : Fin ((m + r) + 1) → P => (w (Fin.tail y) : ℂ))
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        T * (∏ i, (x i : ℕ)) ≤ N * X) →
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        X * Real.exp Δ ≤ ∏ i, (x i : ℝ)) →
      (∀ x, productPrior (Fin.append ν ν) x ≠ 0 → W x ≠ 0 →
        (∏ i, (x i : ℝ)) ≤ X * R) →
      let F : Fin ((m + r) + 1) → (q : P) → ZMod (q : ℕ) → ℂ := primeHalfTests P S favorable
      Real.exp (-(6 * Real.log 2 + 13) * m) ≤
        ‖regularInitialAmplitude P (Fin.append ν ν) (Fin.append F F) ψ X N W‖ := by
  have hbudget := eventual_initial_amplitude_error_budget r z ‖𝓕 ψ 0‖ A B Bs a c δ
    (2 * (Real.log 2 + 2)) hz ha hc hδ (by nlinarith only [hBs])
  filter_upwards [hbudget] with m hbudget
  intro L Y X Δ R hL hLm hmL hY hYL hX hR hgap P _ hP S favorable ν C
    hν hC hbound hnorm hmass w E balanced hw hw1 hbalanced hbalance hE hcE hendpoint hmean
    hsmall N W hcut hlower hupper F
  have hprod : 0 ≤ ∏ i, Fin.append C C i := Finset.prod_nonneg (fun i _ => by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using hC j
    · simpa only [Fin.append_right] using hC j)
  have hs := hbudget L Y X (E.card : ℝ) (∏ i, Fin.append C C i)
    (∑ p : P, (p : ℝ)⁻¹) Δ (m + r) hL hLm hmL hY hYL hX.le le_rfl
    hE hprod hnorm hmass hgap
  have hrate : 2 * (2 * (Real.log 2 + 2)) + 2 * Real.log 2 + 5 =
      6 * Real.log 2 + 13 := by ring
  rw [hrate] at hs
  have hcount : ((m + r) + 1) + ((m + r) + 1) = 2 * (m + (r + 1)) := by omega
  exact primeHalfTests_initialAmplitude_lower_on_support P hP S favorable ν C
    hν hC hbound w hw hw1 E balanced (Real.exp (-(2 * (Real.log 2 + 2)) * m)) δ c
    (Real.exp_nonneg _) hδ.le hc.le hbalanced hbalance hendpoint hmean
    ψ X T R Δ (Real.exp (-(6 * Real.log 2 + 13) * m)) hX hR N hψ hcE
    hcut hsupp hsmall hlower hupper (by simpa only [hcount] using hs)

end Ostmann

end OAI
