import OAI.NumberTheory.TwoPointCorrelations.HalaszLocalMean
import OAI.NumberTheory.TwoPointCorrelations.MRTTypicalWindow

namespace OAI

/-! Actual cofactor bounds with a local frequency hypothesis. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical ComplexConjugate

theorem halasz_local_count_window :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (Q P : Finset ℕ), (∀ p ∈ Q, p.Prime) → (∀ p ∈ P, p.Prime) →
    ∀ (t M : ℝ), 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 →
        2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤ C *
        ((M + 1) * Real.exp (-M) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  obtain ⟨C, X₁, hC, hmean⟩ := halasz_local_count_prefix
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  refine ⟨15 * C, K, max X₁ (Real.exp 2), by positivity, hK, ?_⟩
  intro N a ha hX F hF1 hFm hFb Q P hQ hP t M hM hd
  let m := ⌊(N : ℝ) / a⌋₊
  let n := ⌊(2 * N : ℝ) / a⌋₊
  have hmX : X₁ ≤ (m : ℝ) := (le_max_left _ _).trans hX
  have hme : Real.exp 2 ≤ (m : ℝ) := (le_max_right _ _).trans hX
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hm2 : 2 ≤ m := by exact_mod_cast (he2.trans hme)
  have ha0 : 0 < a := by linarith
  have hx : 2 ≤ (N : ℝ) / a :=
    (he2.trans hme).trans (Nat.floor_le (div_nonneg (Nat.cast_nonneg N) ha0.le))
  obtain ⟨hm0, hmn, hn3⟩ := mrt_cofactor_window_ratio N ha0 hx
  change 0 < m at hm0
  change m ≤ n at hmn
  change n ≤ 3 * m at hn3
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hm0.trans_le hmn
  have hln : 2 ≤ Real.log (n : ℝ) := by
    apply (Real.le_log_iff_exp_le hn0).mpr
    exact hme.trans (by exact_mod_cast hmn)
  have hlln : 0 ≤ Real.log (Real.log (n : ℝ)) := Real.log_nonneg (by linarith)
  let D := (M + 1) * Real.exp (-M)
  let E := Real.log (Real.log (n : ℝ)) / Real.log (n : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := div_nonneg hlln (by linarith)
  have hbound := mrt_cofactor_bound_of_prefix P (mrtMissingCoefficient F Q) N ha hx t
    (A := 3 * C * (D + E)) (by positivity) ?_
  · change ‖mrtCofactorPolynomial P (mrtMissingCoefficient F Q) N a t‖ ≤
      (15 * C) * (D + E)
    exact hbound.trans_eq (by ring)
  · intro k hk
    change k ∈ Icc m n at hk
    obtain ⟨hmk, hkn⟩ := mem_Icc.mp hk
    have hk2 : 2 ≤ k := hm2.trans hmk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hkn3 : n ≤ k ^ 3 := by
      have hkSq : 3 ≤ k ^ 2 := by nlinarith
      calc
        n ≤ 3 * m := hn3
        _ ≤ 3 * k := Nat.mul_le_mul_left 3 hmk
        _ ≤ k * k ^ 2 := by nlinarith
        _ = k ^ 3 := by ring
    have hlog : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hk0 (by exact_mod_cast hkn)
    have hlog0 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
    have hdk : ∀ v : ℝ, |v-t| ≤ Real.log (k:ℝ)^8 →
        2*M ≤ squaredDistance F (mrtArchimedeanTwist v) k := by
      intro v hv
      have hdist := hcut F hFb k n hk2 hkn hkn3 v
      have hlow := hd v (hv.trans (pow_le_pow_left₀ hlog0 hlog 8))
      change 2*M+K ≤ squaredDistance F (mrtArchimedeanTwist v) n at hlow
      linarith
    have hpref := hmean k (hmX.trans (by exact_mod_cast hmk)) F hF1 hFm hFb Q P hQ hP
      t M hM hdk
    have herror := halasz_log_error_cutoff hk2 hkn hkn3 hlln
    change Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) ≤ 3 * E at herror
    calc
      _ ≤ C * k * (D + Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) := hpref
      _ ≤ C * k * (D + 3 * E) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) (by positivity)
      _ ≤ C * k * (3 * (D + E)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = (3 * C * (D + E)) * k := by ring

/-- Remaining-band inclusion--exclusion preserves the local frequency window. -/
theorem halasz_local_typical_window :
    ∃ C K X₀ : ℝ, 0 < C ∧ 0 ≤ K ∧
    ∀ (N : ℕ) (a : ℝ), 1 ≤ a → X₀ ≤ (⌊(N : ℝ) / a⌋₊ : ℝ) →
    ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
    ∀ (ι : Type*) (J : Finset ι) (P : ι → Finset ℕ) (Q : Finset ℕ),
      (∀ j ∈ J, ∀ p ∈ P j, p.Prime) → (∀ p ∈ Q, p.Prime) →
    ∀ (t M : ℝ), 0 ≤ M →
      (∀ v : ℝ, |v-t| ≤ Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ) ^ 8 →
        2 * M + K ≤ squaredDistance F (mrtArchimedeanTwist v) ⌊(2 * N : ℝ) / a⌋₊) →
      ‖mrtCofactorPolynomial Q (mrtTypicalCoefficient J P F) N a t‖ ≤
        (2 : ℝ) ^ J.card * C * ((M + 1) * Real.exp (-M) +
          Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
            Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
  obtain ⟨C, K, X₀, hC, hK, hb⟩ := halasz_local_count_window
  refine ⟨C, K, X₀, hC, hK, ?_⟩
  intro N a ha hN F hF1 hFm hFb ι J P Q hP hQ t M hM hd
  rw [mrt_typical_cofactor_expansion]
  calc
    _ ≤ ∑ I ∈ J.powerset,
        ‖(-1 : ℂ) ^ I.card *
          mrtCofactorPolynomial Q (mrtMissingCoefficient F (I.biUnion P)) N a t‖ :=
      norm_sum_le _ _
    _ ≤ ∑ I ∈ J.powerset, C * ((M + 1) * Real.exp (-M) +
        Real.log (Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) /
          Real.log (⌊(2 * N : ℝ) / a⌋₊ : ℝ)) := by
      apply sum_le_sum
      intro I hI
      rw [norm_mul, norm_pow]
      simp only [norm_neg, norm_one, one_pow, one_mul]
      apply hb N a ha hN F hF1 hFm hFb (I.biUnion P) Q _ hQ t M hM hd
      intro p hp
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hp
      exact hP j ((mem_powerset.mp hI) hj) p hpj
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, card_powerset, Nat.cast_pow, Nat.cast_ofNat]
      ring


end TwoPointCorrelations

end OAI
