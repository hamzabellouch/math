import OAI.Geometry.EinsteinFour.ScalarOpenIntegerEllipticGain

namespace OAI

/-! A fixed local elliptic operator gains two derivatives at every step of
its inhomogeneous resolvent chain. The estimates stay on one open ball. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_iterate_open_integer_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (κ : ℂ) (u : ℕ → T)
    (hu : ∀ k, MemSobolev 1 2 (u k))
    (heq : ∀ k (ψ : S), HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2) →
      (scalarPerturbedOperator a b (u (k + 1)) - u (k + 1) - M c (u (k + 1))) ψ =
        κ * u k ψ)
    (n : ℕ) (φ : S) (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ ball 0 (1 / 2)) :
    MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2 (M φ (u n)) := by
  induction n generalizing φ with
  | zero =>
      simpa only [Nat.mul_zero, zero_add, Nat.cast_one] using
        scalar_memSobolev_schwartz_multiplier 1 φ (u 0) (by simpa only [Nat.cast_one] using hu 0)
  | succ n ih =>
      have hf (ψ : S) (hψc : HasCompactSupport (ψ : V → ℂ))
          (hψs : tsupport (ψ : V → ℂ) ⊆ ball 0 (1 / 2)) :
          MemSobolev ((2 * n + 1 : ℕ) : ℝ) 2
            (M ψ (scalarPerturbedOperator a b (u (n + 1)) - u (n + 1) - M c (u (n + 1)))) := by
        have he : M ψ (scalarPerturbedOperator a b (u (n + 1)) - u (n + 1) - M c (u (n + 1))) =
            M ψ (κ • u n) :=
          scalar_localize_eq_of_tests (ball 0 (1 / 2)) _ (κ • u n)
            (fun η hηc hηs => heq n η hηc hηs) ψ hψc hψs
        rw [he, map_smul]
        exact (ih ψ hψc hψs).smul κ
      have hg := scalar_half_open_integer_forcing_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
        (2 * n + 1) c (u (n + 1)) (hu (n + 1)) hf φ hc hs
      convert hg using 1
      push_cast
      ring

end
end PositiveEinsteinFour.Geometry

end OAI
