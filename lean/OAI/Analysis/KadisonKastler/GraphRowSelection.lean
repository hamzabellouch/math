import OAI.Analysis.KadisonKastler.GraphRowMoments

namespace OAI

/-! # Selecting a replicated row with a uniform fourth-moment cost

The row length cancels against the small left vector-state variance of
the flattened element. The resulting constant is independent of the
rescaling parameter and the row length.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem rowLimit_numeric_bound {k α β D E : ℝ}
    (hk : 1 ≤ k) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsize : α + k * β ≤ 240)
    (hD : D ≤ 128 ^ 2 * β) (hE : E ≤ 128 ^ 2 * α) :
    k * D + k * (k - 1) * β ^ 2 + E + (k - 1) * (α * β) < 16777216 := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hb0 : 0 ≤ k * β := mul_nonneg hk0 hβ
  have ha1 : α ≤ 240 := by linarith
  have hb1 : k * β ≤ 240 := by linarith
  have hkd := mul_le_mul_of_nonneg_left hD hk0
  have hpair : k * (k - 1) * β ^ 2 ≤ (k * β) ^ 2 := by
    nlinarith [mul_nonneg hk0 (sq_nonneg β)]
  have hcross : (k - 1) * (α * β) ≤ α * (k * β) := by
    nlinarith [mul_nonneg hα hβ]
  have hbsq : (k * β) ^ 2 ≤ 240 ^ 2 := by nlinarith
  have hab : α * (k * β) ≤ 240 ^ 2 := by
    exact (mul_le_mul ha1 hb1 hb0 (by norm_num)).trans_eq (by norm_num)
  nlinarith

/-- For every flattened element, an actual finite matrix-orbit row has
uniformly bounded cost. The row length is exactly the square rescaling. -/
theorem exists_matrixGraphRow_cost_le
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    {k : ℕ} (hk : 0 < k) (z : H →L[ℂ] H) (hz : z ∈ M)
    (hznorm : ‖z‖ ≤ 128) (hzsize : ‖z Ω‖ ^ 2 + k * ‖star z Ω‖ ^ 2 ≤ 240) :
    ∃ j, ∃ ω : Fin k → SignedPermutation (Fin (d j)),
      graphRowCost Ω (matrixGraphRow (E j) z ω) ≤ 16777216 := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hD := realVectorState_reverse_fourth_le_norm_sq Ω z
  have hF := realVectorState_fourth_le_norm_sq Ω z
  have hnorm2 : ‖z‖ ^ 2 ≤ (128 : ℝ) ^ 2 := by nlinarith [norm_nonneg z]
  have hD' : realVectorState Ω ((z * star z) ^ 2) ≤ 128 ^ 2 * ‖star z Ω‖ ^ 2 :=
    hD.trans (mul_le_mul_of_nonneg_right hnorm2 (sq_nonneg _))
  have hF' : realVectorState Ω ((star z * z) ^ 2) ≤ 128 ^ 2 * ‖z Ω‖ ^ 2 :=
    hF.trans (mul_le_mul_of_nonneg_right hnorm2 (sq_nonneg _))
  have hL := rowLimit_numeric_bound (k := (k : ℝ)) (α := ‖z Ω‖ ^ 2)
    (β := ‖star z Ω‖ ^ 2) (by exact_mod_cast hk) (sq_nonneg _) (sq_nonneg _)
    hzsize hD' hF'
  have ht := matrixGraphRow_cost_tendsto M Ω hΩ (I := Fin k) d E hmono hEM hirr hc z hz
  simp only [Fintype.card_fin] at ht
  have hpow : ‖star z Ω‖ ^ 4 = (‖star z Ω‖ ^ 2) ^ 2 := by ring
  rw [hpow] at ht
  have he := ht.eventually (gt_mem_nhds hL)
  obtain ⟨j, hj⟩ := he.exists
  obtain ⟨ω, _, hω⟩ := Finset.exists_le_of_expect_le
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin k → SignedPermutation (Fin (d j)))).Nonempty)
    hj.le
  exact ⟨j, ω, hω⟩

end

end KadisonKastler

end OAI
