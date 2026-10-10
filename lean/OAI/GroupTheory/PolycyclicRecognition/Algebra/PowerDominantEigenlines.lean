import OAI.GroupTheory.PolycyclicRecognition.Algebra.TransverseEigenlineFreePair

namespace OAI

/-! # Dominance with a fixed multiplicative constant

A bounded change of coordinates multiplies a kernel estimate by a constant.
A common positive power absorbs all four constants before applying ping-pong.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter

theorem scaled_spectral_gap_eventually (a b C : ℝ) (hb : 0 ≤ b) (hgap : b < |a|) :
    ∀ᶠ n : ℕ in atTop, C * b ^ n < |a ^ n| := by
  have ha : 0 < |a| := hb.trans_lt hgap
  have ht : Tendsto (fun n : ℕ => C * (b / |a|) ^ n) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg hb ha.le) ((div_lt_one ha).mpr hgap)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
  rw [div_pow, ← mul_div_assoc] at hn
  have hp : 0 < |a| ^ n := pow_pos ha n
  simpa only [one_mul, abs_pow] using (div_lt_iff₀ hp).mp hn

theorem eigenline_vector_power {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : V →L[ℝ] V) (v : V) (a : ℝ) (hv : T v = a • v) (n : ℕ) :
    (T ^ n) v = a ^ n • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change T ((T ^ n) v) = _
    rw [ih, map_smul, hv, smul_smul, pow_succ]

variable {G V : Type} [Group G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MulAction G V]

theorem free_powers_of_asymptotically_dominant_eigenlines
    (ρ : G →* (V →L[ℝ] V)) (hact : ∀ g x, ρ g x = g • x)
    (a : Bool → G) (φ : Bool → Bool → V →L[ℝ] ℝ) (v : Bool → Bool → V)
    (μ b C : Bool → Bool → ℝ)
    (hv : ∀ i s, ρ (signedPingPongGenerator a i s) (v i s) = μ i s • v i s)
    (hφv : ∀ i s, φ i s (v i s) = 1)
    (hφ : ∀ i s x, φ i s (ρ (signedPingPongGenerator a i s) x) = μ i s * φ i s x)
    (hb : ∀ i s, 0 ≤ b i s) (hgap : ∀ i s, b i s < |μ i s|)
    (hC : ∀ i s, 0 ≤ C i s)
    (hker : ∀ i s n x, φ i s x = 0 →
      ‖(ρ (signedPingPongGenerator a i s) ^ n) x‖ ≤ C i s * b i s ^ n * ‖x‖)
    (htrans : ∀ i s j t, i ≠ j → φ i s (v j t) ≠ 0)
    (hlines : ∀ i s j t, i ≠ j →
      v j t ∉ Submodule.span ℝ ({v i s} : Set V)) :
    ∃ N : ℕ, 0 < N ∧ Function.Injective (FreeGroup.lift (fun i => (a i) ^ N)) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i s, C i s * b i s ^ n < |μ i s ^ n| := by
    apply (Filter.eventually_all).mpr
    intro i
    apply (Filter.eventually_all).mpr
    intro s
    exact scaled_spectral_gap_eventually _ _ _ (hb i s) (hgap i s)
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
    exact eigenline_functional_power _ _ _ (hφ i s) N x
  have hkN (i s : Bool) (x : V) (hx : φ i s x = 0) :
      ‖ρ (signedPingPongGenerator aN i s) x‖ ≤ C i s * b i s ^ N * ‖x‖ := by
    rw [hs, map_pow]
    exact hker i s N x hx
  obtain ⟨M, hM, hfree⟩ := free_powers_of_transverse_dominant_eigenlines ρ hact aN φ v
    (fun i s => μ i s ^ N) (fun i s => C i s * b i s ^ N) hvN hφv hφN
    (fun i s => mul_nonneg (hC i s) (pow_nonneg (hb i s) N)) hNgap hkN htrans hlines
  refine ⟨N * M, Nat.mul_pos hN hM, ?_⟩
  simpa only [aN, pow_mul] using hfree

end PolycyclicRecognition

end

end OAI
