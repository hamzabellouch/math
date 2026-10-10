import OAI.Analysis.KadisonKastler.Column

namespace OAI

/-!
# Square sums over orthogonal supports

These are the Hilbert-space estimates converting bounds through each
diagonal label into the uniform coefficient-column drift in §3.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sum_sq_of_pairwise_orthogonal {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have horth : inner ℂ (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      apply sum_eq_zero
      intro i hi
      exact hv a (by simp) i (by simp [hi]) (by aesop)
    rw [sum_insert ha, norm_add_sq (𝕜 := ℂ), horth]
    rw [ih (by intro i hi j hj hij; exact hv i (by simp [hi]) j (by simp [hj]) hij),
      sum_insert ha]
    simp only [map_zero, mul_zero, add_zero]

/-- A bound on the squared weights through each label controls the sum
over all supports. Each support is counted just once. -/
theorem weighted_orthogonal_supports_le {ι ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype ω]
    (v : ι → H) (S : ω → Finset ι) (β : ω → ℝ) {B : ℝ}
    (hv : Pairwise (fun i j => inner ℂ (v i) (v j) = 0))
    (hβ : ∀ i, (∑ w : ω, if i ∈ S w then β w ^ 2 else 0) ≤ B) :
    (∑ w : ω, β w ^ 2 * ‖∑ i ∈ S w, v i‖ ^ 2) ≤
      B * ‖∑ i : ι, v i‖ ^ 2 := by
  classical
  have hn (s : Finset ι) : ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 :=
    norm_sum_sq_of_pairwise_orthogonal s v (fun i _ j _ hij => hv hij)
  calc
    _ = ∑ w : ω, ∑ i : ι, (if i ∈ S w then β w ^ 2 else 0) * ‖v i‖ ^ 2 := by
      apply sum_congr rfl
      intro w _
      rw [hn, mul_sum]
      simp only [ite_mul, zero_mul]
      rw [← sum_filter]
      simp
    _ = ∑ i : ι, (∑ w : ω, if i ∈ S w then β w ^ 2 else 0) * ‖v i‖ ^ 2 := by
      rw [sum_comm]
      simp only [sum_mul]
    _ ≤ ∑ i : ι, B * ‖v i‖ ^ 2 := by
      apply sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hβ i) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, hn]

variable [CompleteSpace H]

theorem orthogonal_projection_vectors {ι : Type*} (P : ι → H →L[ℂ] H)
    (hself : ∀ i, IsSelfAdjoint (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (x : H) :
    Pairwise (fun i j => inner ℂ (P i x) (P j x) = 0) := by
  intro i j hij
  have hstar : (P i).adjoint = P i := (hself i).star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar]
  have hz : P i (P j x) = 0 := by
    change (P i * P j) x = 0
    rw [horth i j hij]
    rfl
  rw [hz, inner_zero_right]

/-- The support-weighted estimate for an actual orthogonal partition of
the identity in an operator algebra. -/
theorem weighted_projection_supports_le {ι ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype ω]
    (P : ι → H →L[ℂ] H) (S : ω → Finset ι) (β : ω → ℝ) {B : ℝ}
    (hself : ∀ i, IsSelfAdjoint (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (htotal : ∑ i, P i = 1)
    (hβ : ∀ i, (∑ w : ω, if i ∈ S w then β w ^ 2 else 0) ≤ B) (x : H) :
    (∑ w : ω, β w ^ 2 * ‖(∑ i ∈ S w, P i) x‖ ^ 2) ≤ B * ‖x‖ ^ 2 := by
  have h := weighted_orthogonal_supports_le (fun i => P i x) S β
    (orthogonal_projection_vectors P hself horth x) hβ
  simpa only [← _root_.sum_apply, htotal, one_apply_eq_self] using h

/-- The through-label square bound `64`, together with the cyclic
column constant `8`, gives the coefficient drift constant `64`. -/
theorem support_drift_le_sixty_four {ι ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype ω]
    (P : ι → H →L[ℂ] H) (S : ω → Finset ι) (β : ω → ℝ)
    (hself : ∀ i, IsSelfAdjoint (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (htotal : ∑ i, P i = 1)
    (hβ : ∀ i, (∑ w : ω, if i ∈ S w then β w ^ 2 else 0) ≤ 64)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (D : ω → H) (x : H)
    (hD : ∀ w, ‖D w‖ ≤ 8 * δ * β w * ‖(∑ i ∈ S w, P i) x‖) :
    ‖WithLp.toLp 2 D‖ ≤ 64 * δ * ‖x‖ := by
  have hsum := weighted_projection_supports_le P S β hself horth htotal hβ x
  have hsq : ‖WithLp.toLp 2 D‖ ^ 2 ≤ (64 * δ * ‖x‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ w : ω, (8 * δ * β w * ‖(∑ i ∈ S w, P i) x‖) ^ 2 := by
        apply sum_le_sum
        intro w _
        exact pow_le_pow_left₀ (norm_nonneg _) (hD w) 2
      _ = (8 * δ) ^ 2 * ∑ w : ω, β w ^ 2 * ‖(∑ i ∈ S w, P i) x‖ ^ 2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro w _
        ring
      _ ≤ (8 * δ) ^ 2 * (64 * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
      _ = _ := by ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

omit [CompleteSpace H] in
/-- Applying one bounded operator in every component has the same bound
on the Hilbert direct sum. -/
theorem norm_pointwise_operator_le {ω : Type*} [Fintype ω]
    (T : H →L[ℂ] H) (v : ω → H) :
    ‖WithLp.toLp 2 (fun w => T (v w))‖ ≤ ‖T‖ * ‖WithLp.toLp 2 v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, mul_sum]
  apply sum_le_sum
  intro w _
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm (v w)) 2

omit [CompleteSpace H] in
/-- A contractive column of coefficients costs at most twice the norm
of a perturbation when commuting that perturbation past the column. -/
theorem norm_column_commutator_le {ω : Type*} [Fintype ω]
    (K : ω → H →L[ℂ] H)
    (hK : ∀ y : H, ‖WithLp.toLp 2 (fun w => K w y)‖ ≤ ‖y‖)
    (T : H →L[ℂ] H) (x : H) :
    ‖WithLp.toLp 2 (fun w => (T * K w - K w * T) x)‖ ≤ 2 * ‖T‖ * ‖x‖ := by
  have heq : WithLp.toLp 2 (fun w => (T * K w - K w * T) x) =
      WithLp.toLp 2 (fun w => T (K w x)) - WithLp.toLp 2 (fun w => K w (T x)) := rfl
  rw [heq]
  calc
    _ ≤ ‖WithLp.toLp 2 (fun w => T (K w x))‖ +
        ‖WithLp.toLp 2 (fun w => K w (T x))‖ := norm_sub_le _ _
    _ ≤ ‖T‖ * ‖WithLp.toLp 2 (fun w => K w x)‖ + ‖T x‖ :=
      add_le_add (norm_pointwise_operator_le T _) (hK (T x))
    _ ≤ ‖T‖ * ‖x‖ + ‖T‖ * ‖x‖ := add_le_add
      (mul_le_mul_of_nonneg_left (hK x) (norm_nonneg T)) (T.le_opNorm x)
    _ = _ := by ring

omit [CompleteSpace H] in
/-- The `64δ` bound obtained after averaging changes to `66δ` for the
original implementing operator. -/
theorem coefficient_drift_le_sixty_six {ω : Type*} [Fintype ω]
    (K : ω → H →L[ℂ] H)
    (hK : ∀ y : H, ‖WithLp.toLp 2 (fun w => K w y)‖ ≤ ‖y‖)
    (h h0 : H →L[ℂ] H) {δ : ℝ} (hclose : ‖h - h0‖ ≤ δ)
    (x : H)
    (hbound : ‖WithLp.toLp 2 (fun w => (h0 * K w - K w * h0) x)‖ ≤
      64 * δ * ‖x‖) :
    ‖WithLp.toLp 2 (fun w => (h * K w - K w * h) x)‖ ≤ 66 * δ * ‖x‖ := by
  have heq : WithLp.toLp 2 (fun w => (h * K w - K w * h) x) =
      WithLp.toLp 2 (fun w => (h0 * K w - K w * h0) x) +
      WithLp.toLp 2 (fun w => ((h - h0) * K w - K w * (h - h0)) x) := by
    ext w
    change (h * K w - K w * h) x =
      ((h0 * K w - K w * h0) + ((h - h0) * K w - K w * (h - h0))) x
    congr 1
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖WithLp.toLp 2 (fun w => (h0 * K w - K w * h0) x)‖ +
        ‖WithLp.toLp 2 (fun w => ((h - h0) * K w - K w * (h - h0)) x)‖ :=
      norm_add_le _ _
    _ ≤ 64 * δ * ‖x‖ + 2 * ‖h - h0‖ * ‖x‖ :=
      add_le_add hbound (norm_column_commutator_le K hK (h - h0) x)
    _ ≤ 64 * δ * ‖x‖ + 2 * δ * ‖x‖ := by gcongr
    _ = _ := by ring

end

end KadisonKastler

end OAI
