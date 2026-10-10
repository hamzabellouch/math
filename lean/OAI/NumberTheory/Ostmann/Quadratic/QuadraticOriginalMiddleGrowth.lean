import OAI.NumberTheory.Ostmann.Quadratic.QuadraticOriginalCutoffGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWholeSmallHighGrowth
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticWholeSmallMiddleGrowth

namespace OAI

/-! # Every full correction uses its original frequency-dependent cutoff -/

namespace Ostmann

open scoped Classical BigOperators SchwartzMap

theorem quadratic_whole_original_middle_growth (ρ : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 1 ≤ |a|) :
    ∃ Cu Cb : ℝ, 0 ≤ Cu ∧ 0 ≤ Cb ∧ ∀ C ε ξ M H J : ℝ, 0 ≤ C →
      ∀ e B N Q L : ℕ, 0 < M → 0 < H → (N : ℝ) ≤ 2 * H →
      0 < e → 0 < B → 0 < N → 1 ≤ Q → 1 ≤ J →
      ∀ R : ℕ → ℕ → Prop, ∀ v w : ℕ → ℂ,
      (∀ n < N, v n = 0) → (∀ n < N, w n = 0) →
      (∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
        (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) →
      ‖((Real.sqrt M / Real.sqrt e : ℝ) : ℂ) *
          quadraticMiddleCorrectionTotal ρ a ha M e B N Q L
            (fun d b => R d b ∧ quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) ∧
              (d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J) v w‖ ≤
        (128 * (2 * J) * (2 * L + 1) * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticCorrectionGrowthScale C ε ξ M e B N v w) *
            (Cu + ((Nat.log 2 Q + 1 : ℕ) : ℝ) * Cb) := by
  obtain ⟨Cu, Cb, hCu, hCb, hc⟩ := quadratic_whole_middle_growth ρ a ha
  refine ⟨Cu, Cb, hCu, hCb, ?_⟩
  intro C ε ξ M H J hC e B N Q L hM hH hNH he hB hN hQ hJ R v w hv hw hmat
  apply hc C ε ξ M (2 * J) hC e B N Q L hM he hB hN hQ (by linarith) _ v w hv hw _ hmat
  intro d _ b hb hbB hp
  exact quadratic_original_lower_cut hM hH (by exact_mod_cast hN) hNH he hB hJ hbB
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2 hp.2.1

theorem quadratic_whole_original_small_high_growth {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallHighTotal E B N Q
        (fun d b => R d b ∧ quadraticSecondUpper (quadraticSmallScale M b) J < (E * d : ℕ)) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  apply quadratic_whole_small_high_growth hC hM hE hB hN hQ hJ _ v w _ hmat
  intro d _ b hb _ hp
  exact quadratic_small_high_implies_lower hM
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).1 hJ hp.2

theorem quadratic_whole_original_small_middle_growth (ρ : 𝓢(ℝ, ℂ))
    {C ε ξ M J : ℝ} (hC : 0 ≤ C)
    {E B N Q L : ℕ} (hM : 0 < M) (hE : 1 ≤ E) (hB : 0 < B) (hN : 0 < N) (hQ : 1 ≤ Q)
    (hJ : 1 ≤ J) (R : ℕ → ℕ → Prop) (v w : ℕ → ℂ)
    (hmat : ∀ i ≤ Nat.log 2 (2 * N), QuadraticSieveBound (2 * B) (2 * N / 2 ^ i)
      (quadraticGrowthCutoff C ε ξ (2 * B) (2 * N) i)) :
    ‖(Real.sqrt M : ℂ) * quadraticSmallMiddleTotal ρ M E B N Q L
        (fun d b => R d b ∧ quadraticSecondLower (quadraticSmallScale M b) J < (E * d : ℕ) ∧
          (E * d : ℕ) ≤ quadraticSecondUpper (quadraticSmallScale M b) J) v w‖ ≤
      ((Nat.log 2 Q + 2 : ℕ) : ℝ) *
        (16 * (2 * L + 1) * quadraticSmallFourierBound ρ * ((Nat.log 2 (2 * N) + 1 : ℕ) : ℝ) ^ 2 *
          quadraticSmallCorrectionGrowthScale C ε ξ M (8 * E * J) B N v w) := by
  apply quadratic_whole_small_middle_growth ρ hC hM hE hB hN hQ hJ _ v w _ hmat
  intro d _ b _ _ hp
  exact hp.2.1

end Ostmann

end OAI
