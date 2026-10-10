import OAI.Analysis.KadisonKastler.GraphDirectionalBound

namespace OAI

/-! # Uniform row flattening at arbitrary large rescalings

Rounding the squared rescaling up changes the moment normalization by at
most a factor two. The same fixed row cutoff remains sufficient.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

private theorem rowLimit_numeric_bound_480 {k α β D E : ℝ}
    (hk : 1 ≤ k) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hsize : α + k * β ≤ 480)
    (hD : D ≤ 128 ^ 2 * β) (hE : E ≤ 128 ^ 2 * α) :
    k * D + k * (k - 1) * β ^ 2 + E + (k - 1) * (α * β) < 16777216 := by
  have hk0 : 0 ≤ k := zero_le_one.trans hk
  have hb0 : 0 ≤ k * β := mul_nonneg hk0 hβ
  have ha1 : α ≤ 480 := by linarith
  have hb1 : k * β ≤ 480 := by linarith
  have hkd := mul_le_mul_of_nonneg_left hD hk0
  have hpair : k * (k - 1) * β ^ 2 ≤ (k * β) ^ 2 := by
    nlinarith [mul_nonneg hk0 (sq_nonneg β)]
  have hcross : (k - 1) * (α * β) ≤ α * (k * β) := by
    nlinarith [mul_nonneg hα hβ]
  have hbsq : (k * β) ^ 2 ≤ 480 ^ 2 := by nlinarith
  have hab : α * (k * β) ≤ 480 ^ 2 := by
    exact (mul_le_mul ha1 hb1 hb0 (by norm_num)).trans_eq (by norm_num)
  nlinarith

/-- For every flattened element, an actual finite matrix-orbit row has
uniformly bounded cost. The row length is exactly the square rescaling. -/
theorem exists_matrixGraphRow_cost_le_480
    (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    {k : ℕ} (hk : 0 < k) (z : H →L[ℂ] H) (hz : z ∈ M)
    (hznorm : ‖z‖ ≤ 128) (hzsize : ‖z Ω‖ ^ 2 + k * ‖star z Ω‖ ^ 2 ≤ 480) :
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
  have hL := rowLimit_numeric_bound_480 (k := (k : ℝ)) (α := ‖z Ω‖ ^ 2)
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


/-- Increasing the square of the graph scale increases its norm. -/
theorem norm_rescaledGraphVector_mono_square
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c b : ℝ} (hcb : c ^ 2 ≤ b ^ 2)
    (x : H →L[ℂ] H) :
    ‖rescaledGraphVector J Ω c x‖ ≤ ‖rescaledGraphVector J Ω b x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_rescaledGraphVector_sq, norm_rescaledGraphVector_sq]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcb (sq_nonneg _))

/-- At a scale whose square is at most the row length, the same cutoff
has the same normalized graph error bound. -/
theorem clippedGraphRow_error_le_scale {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c : ℝ} (hc : c ^ 2 ≤ (k : ℝ))
    (Y : Fin k → H →L[ℂ] H) (hcost : graphRowCost Ω Y ≤ 16777216) :
    finiteRMS (fun i => rescaledGraphVector J Ω c
      (Y i - clippedGraphRow 131072 Y i)) ≤ 1 / 32 := by
  apply (finiteRMS_mono _ _ ?_).trans (clippedGraphRow_error_le hk J Ω Y hcost)
  intro i
  apply norm_rescaledGraphVector_mono_square J Ω
  simpa only [Real.sq_sqrt (Nat.cast_nonneg k)] using hc

/-- The retained signal estimate at every graph scale up to sqrt(k). -/
theorem clippedGraphRow_signal_le_scale {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c : ℝ} (hc : c ^ 2 ≤ (k : ℝ))
    (T : TomitaGraphHilbert H →L[ℂ] TomitaGraphHilbert H)
    (Y : Fin k → H →L[ℂ] H) (hcost : graphRowCost Ω Y ≤ 16777216)
    (hsignal : ‖T‖ / 8 ≤ finiteRMS (fun i => T (rescaledGraphVector J Ω c (Y i)))) :
    ‖T‖ / 16 ≤ finiteRMS (fun i =>
      T (rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i))) := by
  let v := fun i => T (rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i))
  let w := fun i => T (rescaledGraphVector J Ω c (Y i - clippedGraphRow 131072 Y i))
  have he : (fun i => T (rescaledGraphVector J Ω c (Y i))) = (fun i => v i + w i) := by
    funext i
    have h := (rescaledGraphOperatorMap J Ω c).map_sub (Y i) (clippedGraphRow 131072 Y i)
    change rescaledGraphVector J Ω c (Y i - clippedGraphRow 131072 Y i) =
      rescaledGraphVector J Ω c (Y i) - rescaledGraphVector J Ω c (clippedGraphRow 131072 Y i) at h
    dsimp [v, w]
    rw [h, map_sub]
    abel
  have hw : finiteRMS w ≤ ‖T‖ * (1 / 32) :=
    (finiteRMS_apply_le T _).trans (mul_le_mul_of_nonneg_left
      (clippedGraphRow_error_le_scale hk J Ω hc Y hcost) (norm_nonneg T))
  rw [he] at hsignal
  have ht := finiteRMS_add_le v w
  change ‖T‖ / 16 ≤ finiteRMS v
  nlinarith [norm_nonneg T]

/-- The normalized graph metric is controlled by the whole row norm at
any graph scale whose square is at most its length. -/
theorem graphRowRMS_le_scale {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {c : ℝ} (hc : c ^ 2 ≤ (k : ℝ))
    (Y : Fin k → H →L[ℂ] H) :
    finiteRMS (fun i => rescaledGraphVector J Ω c (Y i)) ≤
      Real.sqrt 2 * ‖operatorRow Y‖ * ‖Ω‖ := by
  apply (finiteRMS_mono _ _ ?_).trans (graphRowRMS_le hk J Ω Y)
  intro i
  apply norm_rescaledGraphVector_mono_square J Ω
  simpa only [Real.sq_sqrt (Nat.cast_nonneg k)] using hc

end

end KadisonKastler

end OAI
