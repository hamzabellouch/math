import OAI.Geometry.EinsteinFour.ScalarPoissonKernelPotential

namespace OAI

/-! Local H3 elliptic gain for an actual first-order Sobolev source. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution Set Metric
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "S" => 𝓢(V, ℂ)
local notation "T" => 𝓢'(V, ℂ)
local notation "D" => scalarSchwartzCoordinateDerivative
local notation "M" => smulLeftCLM ℂ

theorem scalar_localize_eq_of_tests (U : Set V) (u f : T)
    (htest : ∀ φ : S, HasCompactSupport (φ : V → ℂ) →
      tsupport (φ : V → ℂ) ⊆ U → u φ = f φ)
    (ψ : S) (hc : HasCompactSupport (ψ : V → ℂ))
    (hs : tsupport (ψ : V → ℂ) ⊆ U) : M ψ u = M ψ f := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ ψ φ) = f (SchwartzMap.smulLeftCLM ℂ ψ φ)
  apply htest
  · rw [SchwartzMap.smulLeftCLM_apply ψ.hasTemperateGrowth]
    exact hc.smul_right
  · intro x hx
    exact hs ((SchwartzMap.tsupport_smulLeftCLM_subset (ψ : V → ℂ) φ hx).2)

theorem scalar_ball_H1_forcing_gain
    (a : Fin 4 → Fin 4 → S) (b : Fin 4 → S) (δ : ℝ) (hδ : 0 ≤ δ)
    (ha : ∀ i j x, ‖a i j x‖ ≤ δ)
    (ha1 : ∀ i j k x, ‖D k (a i j) x‖ ≤ δ)
    (ha2 : ∀ i j k l x, ‖D k (D l (a i j)) x‖ ≤ δ)
    (hb : ∀ i x, ‖b i x‖ ≤ δ)
    (hb1 : ∀ i k x, ‖D k (b i) x‖ ≤ δ)
    (hsmall : (16 * (2 * Real.pi) ^ 2 + 36 * (2 * Real.pi) + 20) * δ < 1)
    (c : S) (u f : T) (hf : MemSobolev 1 2 f) (hu : MemSobolev 1 2 u)
    (htest : ∀ ψ : S, HasCompactSupport (ψ : V → ℂ) →
      tsupport (ψ : V → ℂ) ⊆ ball 0 1 →
      (scalarPerturbedOperator a b u - u - M c u) ψ = f ψ)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (φ : S)
    (hc : HasCompactSupport (φ : V → ℂ))
    (hs : tsupport (φ : V → ℂ) ⊆ closedBall 0 r) :
    MemSobolev 3 2 (M φ u) := by
  obtain ⟨ψ, hψ, hnest, hsupp⟩ := exists_scalar_nested_cutoffs r hr0 hr1 φ hc hs
  have hsource (k : ℕ) : MemSobolev 1 2
      (M (ψ k) (scalarPerturbedOperator a b u - u - M c u)) := by
    rw [scalar_localize_eq_of_tests (ball 0 1) _ f htest (ψ k) (hsupp k).1 (hsupp k).2]
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ k) f
      (by simpa only [Nat.cast_one] using hf)
  have houter : MemSobolev 1 2 (M (ψ 2) u) := by
    simpa only [Nat.cast_one] using scalar_memSobolev_schwartz_multiplier 1 (ψ 2) u
      (by simpa only [Nat.cast_one] using hu)
  have hmid : MemSobolev 2 2 (M (ψ 1) u) := by
    have hg := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
      c (ψ 1) (ψ 2) (hnest 1) 0 u (by simpa using houter)
      ((hsource 1).mono (by norm_num))
    simpa using hg
  have hfinal := scalar_nested_cutoff_gain_of_potential a b δ hδ ha ha1 ha2 hb hb1 hsmall
    c (ψ 0) (ψ 1) (hnest 0) 1 u (by simpa using hmid) (by simpa using hsource 0)
  simpa [hψ] using hfinal

end
end PositiveEinsteinFour.Geometry

end OAI
