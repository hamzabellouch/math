import OAI.Geometry.EinsteinFour.ScalarH1EllipticGain

namespace OAI

/-! The nested-cutoff estimate gains two derivatives from an
integer-order source. This is the finite-order bootstrap used for the
linear harmonic two-form equation. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

variable (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
  (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
  (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
  (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
  (hb : ∀ i x, ‖b i x‖ ≤ δ)
  (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
  (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)

include hδ ha ha1 ha2 hb hb1 hsmall in
theorem scalar_finite_cutoff_chain_source_gain (c : S) (u : T)
    (n : ℕ) (ψ : ℕ → S)
    (hnest : ∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1)))
    (hu : MemSobolev 1 2 (M (ψ n) u))
    (hf : ∀ k ≤ n, MemSobolev ((n : ℝ) - 1) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u))) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 0) u) := by
  induction n generalizing ψ with
  | zero => simpa only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add] using hu
  | succ n ih =>
      have ht : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 1) u) := by
        apply ih (fun k => ψ (k + 1))
        · intro k hk
          exact hnest (k + 1) (Nat.succ_lt_succ hk)
        · simpa only [Nat.succ_eq_add_one] using hu
        · intro k hk
          exact (hf (k + 1) (Nat.succ_le_succ hk)).mono (by
            rw [Nat.cast_succ]
            linarith)
      have hs : MemSobolev (n : ℝ) 2
          (M (ψ 0) (scalarPerturbedOperator a b u - u - M c u)) := by
        simpa only [Nat.cast_succ, add_sub_cancel_right] using hf 0 (Nat.zero_le _)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
          c (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u ht hs

include hδ ha ha1 ha2 hb hb1 hsmall in
theorem scalar_ball_integer_forcing_gain (n : ℕ) (c : S) (u f : T)
    (hf : MemSobolev (n : ℝ) 2 f) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = f ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have hsource (k : ℕ) : MemSobolev (n : ℝ) 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u)) := by
    rw [scalar_localize_eq_of_tests (ball 0 1) _ f htest (ψ k) (hsupp k).1 (hsupp k).2]
    exact scalar_memSobolev_schwartz_multiplier n (ψ k) f hf
  have houter : MemSobolev 1 2 (M (ψ (n + 1)) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ (n + 1)) u
      (by simpa only [Nat.cast_one] using hu)
  have hg := scalar_finite_cutoff_chain_source_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c u (n + 1) ψ (fun k _ => hnest k) houter (fun k _ => by
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hsource k)
  simpa only [Nat.add_assoc, Nat.reduceAdd, hψ] using hg

end
end PositiveEinsteinFour.Geometry

end OAI
