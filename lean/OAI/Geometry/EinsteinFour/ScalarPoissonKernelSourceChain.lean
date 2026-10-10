import OAI.Geometry.EinsteinFour.ScalarPoissonKernelLocalizationChain

namespace OAI

/-! The geometric equation has a smooth right-hand side for P - Id.
These localization steps use that remainder and only H1 of the solution. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal Topology

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

/-- Inserting an outer cutoff does not change the inner localization. -/
theorem scalarCutoffNested_mul (ψ χ : S) (h : ScalarCutoffNested ψ χ) (u : T) :
    M ψ (M χ u) = M ψ u := by
  have hm : (χ : V → ℂ) * ψ = ψ := by
    funext x
    by_cases hx : ψ x = 0
    · simp only [Pi.mul_apply, hx, mul_zero]
    · have hmem : x ∈ tsupport (ψ : V → ℂ) := subset_closure hx
      simp only [Pi.mul_apply, (h x hmem).eq_of_nhds, one_mul]
  rw [smulLeftCLM_smulLeftCLM_apply χ.hasTemperateGrowth ψ.hasTemperateGrowth, hm]

/-- One local gain uses a regular remainder P u - u, not an assumption that
P u is already regular to the target order. -/
theorem scalar_nested_cutoff_gain_of_remainder
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (ψ χ : S) (hnest : ScalarCutoffNested ψ χ) (n : ℕ) (u : T)
    (hu : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M χ u))
    (hf : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u - u))) :
    MemSobolev ((n + 2 : ℕ) : ℝ) 2 (M ψ u) := by
  have hinner : MemSobolev ((n + 1 : ℕ) : ℝ) 2 (M ψ u) := by
    rw [← scalarCutoffNested_mul ψ χ hnest]
    exact scalar_memSobolev_schwartz_multiplier (n + 1) ψ _ hu
  have hsource : MemSobolev (n : ℝ) 2 (M ψ (scalarPerturbedOperator a b u)) := by
    have heq : M ψ (scalarPerturbedOperator a b u) =
        M ψ u + M ψ (scalarPerturbedOperator a b u - u) := by
      rw [map_sub]
      abel
    rw [heq]
    exact (hinner.mono (by exact_mod_cast Nat.le_succ n)).add hf
  exact scalar_nested_cutoff_gain a b δ hδ ha ha1 ha2 hb hb1 hsmall ψ χ hnest n u hu hsource

/-- Finite nested localization for the actual smooth remainder P u - u. -/
theorem scalar_finite_cutoff_chain_gain_of_remainder
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
    (hf : ∀ k ≤ n, MemSobolev (n : ℝ) 2 (M (ψ k) (scalarPerturbedOperator a b u - u))) :
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
          (M (ψ 0) (scalarPerturbedOperator a b u - u)) :=
        (hf 0 (Nat.zero_le _)).mono (by exact_mod_cast Nat.le_succ n)
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using
        scalar_nested_cutoff_gain_of_remainder a b δ hδ ha ha1 ha2 hb hb1 hsmall
          (ψ 0) (ψ 1) (hnest 0 (Nat.zero_lt_succ n)) n u htail hsource

/-- The remainder-based finite chains yield every integer order for one
fixed inner cutoff. -/
theorem scalar_cutoff_family_all_orders_of_remainder
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
      (∀ k ≤ n, MemSobolev (n : ℝ) 2 (M (ψ k) (scalarPerturbedOperator a b u - u)))) :
    ∀ n : ℕ, MemSobolev (n : ℝ) 2 (M φ u) := by
  intro n
  obtain ⟨ψ, hψ, hnest, hu, hf⟩ := hchain n
  have hgain := scalar_finite_cutoff_chain_gain_of_remainder a b δ hδ ha ha1 ha2 hb hb1 hsmall
    u n ψ hnest hu hf
  rw [hψ] at hgain
  exact hgain.mono (by exact_mod_cast Nat.le_succ n)

end
end PositiveEinsteinFour.Geometry

end OAI
