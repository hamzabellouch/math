import OAI.Geometry.EinsteinFour.ScalarPoissonKernelLocalization
import OAI.Geometry.EinsteinFour.ScalarPoissonKernelSobolev

namespace OAI

/-! A finite chain of nested cutoffs upgrades local H1 control to every
requested finite Sobolev order. Only the localized equation's right-hand
side needs that order; the starting solution needs one derivative. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

/-- `n` nested transitions upgrade an outer H1 cutoff to H^(n+1) at the
innermost cutoff. The sequence outside the finite chain is irrelevant. -/
theorem scalar_finite_cutoff_chain_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : T) (n : ℕ) (ψ : ℕ → S)
    (hnest : ∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1)))
    (hu : MemSobolev 1 2 (M (ψ n) u))
    (hf : ∀ k ≤ n, MemSobolev (n : ℝ) 2 (M (ψ k) (scalarPerturbedOperator a b u))) :
    MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 0) u) := by
  induction n generalizing ψ with
  | zero => simpa using hu
  | succ n ih =>
      have htail : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M (ψ 1) u) := by
        apply ih (fun k => ψ (k + 1))
        · intro k hk
          exact hnest (k + 1) (Nat.succ_lt_succ hk)
        · simpa only [Nat.succ_eq_add_one] using hu
        · intro k hk
          exact (hf (k + 1) (Nat.succ_le_succ hk)).mono (by
            exact_mod_cast Nat.le_succ n)
      have hsource : MemSobolev (n : ℝ) 2
          (M (ψ 0) (scalarPerturbedOperator a b u)) :=
        (hf 0 (Nat.zero_le _)).mono (by exact_mod_cast Nat.le_succ n)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
          (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u htail hsource

/-- A family of finite localizing chains gives all integer Sobolev orders
for a fixed inner cutoff. This is the form used before Fourier inversion. -/
theorem scalar_cutoff_family_all_orders
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : T) (φ : S)
    (hchain : ∀ n : ℕ, ∃ ψ : ℕ → S, ψ 0 = φ ∧
      (∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      MemSobolev 1 2 (M (ψ n) u) ∧
      (∀ k ≤ n, MemSobolev (n : ℝ) 2 (M (ψ k) (scalarPerturbedOperator a b u)))) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  intro n
  obtain ⟨ψ, hψ, hnest, hu, hf⟩ := hchain n
  have hgain := scalar_finite_cutoff_chain_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall
    u n ψ hnest hu hf
  rw [hψ] at hgain
  exact hgain.mono (by exact_mod_cast Nat.le_succ n)

/-- The regular representative is constructed by the Fourier
Sobolev theorem, once the finite cutoff chains have been supplied. -/
theorem scalar_cutoff_family_smooth_representative
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (u : T) (φ : S)
    (hchain : ∀ n : ℕ, ∃ ψ : ℕ → S, ψ 0 = φ ∧
      (∀ k < n, ScalarCutoffNested (ψ k) (ψ (k + 1))) ∧
      MemSobolev 1 2 (M (ψ n) u) ∧
      (∀ k ≤ n, MemSobolev (n : ℝ) 2 (M (ψ k) (scalarPerturbedOperator a b u)))) :
    ∃ f : V → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ ξ : S, M φ u ξ = ∫ x : V, ξ x * f x :=
  scalar_sobolev_smooth_representative _
    (scalar_cutoff_family_all_orders a b δ hδ ha ha1 ha2 hb hb1 hsmall u φ hchain)

end
end PositiveEinsteinFour.Geometry

end OAI
