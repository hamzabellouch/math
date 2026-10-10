import OAI.GroupTheory.PolycyclicRecognition.Algebra.ValuedEigenlineFreePair

namespace OAI

/-! # Absorbing coordinate-change constants over a normed field -/

noncomputable section
namespace PolycyclicRecognition.ValuedLinearDynamics
open Filter

theorem eigenline_vector_power {K V : Type*} [NormedField K] [NormedAddCommGroup V] [NormedSpace K V]
    (T : V →L[K] V) (v : V) (a : K) (hv : T v = a • v) (n : ℕ) :
    (T ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change T ((T ^ n) v) = _
    rw [ih, map_smul, hv, smul_smul, pow_succ]

variable {K G V : Type} [NontriviallyNormedField K] [CompleteSpace K]
    [Group G] [NormedAddCommGroup V] [NormedSpace K V]
    [FiniteDimensional K V] [MulAction G V]

theorem free_powers_of_asymptotically_dominant_eigenlines
    (ρ : G →* (V →L[K] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[K] K) (v : Bool → Bool → V)
    (μ : Bool → Bool → K) (b C : Bool → Bool → ℝ)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < ‖μ i s‖)
    (hC : ∀ i s, 0 ≤ C i s)
    (hker : ∀ i s n x, φ i s x = 0 →
      ‖(ρ (signedPingPongGenerator a i s) ^ n) x‖ ≤ C i s * b i s ^ n * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → φ i s (v j t) ≠ 0)
    (hlines : ∀ i s j t, i ≠ j →
      v j t ∉ Submodule.span K ({v i s} : Set V)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i s, C i s * b i s ^ n < ‖μ i s ^ n‖ := by
    apply (Filter.eventually_all).mpr
    intro i
    apply (Filter.eventually_all).mpr
    intro s
    have hh := scaled_spectral_gap_eventually ‖μ i s‖ (b i s) (C i s) (hb i s)
      (by simpa only [abs_of_nonneg (norm_nonneg _)] using hgap i s)
    simpa only [abs_pow, abs_of_nonneg (norm_nonneg _), norm_pow] using hh
  obtain ⟨N, hN, hNgap⟩ := ((eventually_gt_atTop 0).and he).exists
  let aN : Bool → G := fun i => a i ^ N
  have hs (i s : Bool) : signedPingPongGenerator aN i s =
      signedPingPongGenerator a i s ^ N := by
    cases s <;> simp [signedPingPongGenerator, aN]
  have hvN (i s : Bool) : ρ (signedPingPongGenerator aN i s) (v i s) =
      μ i s ^ N • v i s := by
    rw [hs, map_pow]
    exact eigenline_vector_power _ _ _ (hv i s) N
  have hφN (i s : Bool) (x : V) : φ i s (ρ (signedPingPongGenerator aN i s) x) =
      μ i s ^ N * φ i s x := by
    rw [hs, map_pow]
    exact functional_power _ _ _ (hφ i s) N x
  have hkN (i s : Bool) (x : V) (hx : φ i s x = 0) :
      ‖ρ (signedPingPongGenerator aN i s) x‖ ≤ C i s * b i s ^ N * ‖x‖ := by
    rw [hs, map_pow]
    exact hker i s N x hx
  obtain ⟨M, hM, hfree⟩ := free_powers_of_transverse_dominant_eigenlines ρ hact aN φ v
    (fun i s => μ i s ^ N) (fun i s => C i s * b i s ^ N) hvN hφv hφN
    (fun i s => mul_nonneg (hC i s) (pow_nonneg (hb i s) N)) hNgap hkN htrans hlines
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  simpa only [aN, pow_mul] using hfree

end PolycyclicRecognition.ValuedLinearDynamics

end

end OAI
