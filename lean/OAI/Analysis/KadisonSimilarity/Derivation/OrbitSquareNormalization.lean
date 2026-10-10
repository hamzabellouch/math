import OAI.Analysis.KadisonSimilarity.Derivation.BoundedHomRow

namespace OAI

/-! Upper and lower orbit estimates for a finite family whose sum of
positive squares is one. This is the normalization step in the cyclic
similarity argument. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem normalized_adjoint_orbit_sum_le (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ∑ i, ‖(π.1 (star (a i))).adjoint ξ‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
  obtain ⟨f, g, hf, hg, hfg⟩ := boundedHom_vector_states
    littleGrothendieck_proved π hM hπ ξ
  have hf' : (∑ i, (f (star (a i) * a i)).re) ≤ 1 := by
    rw [← Complex.re_sum, ← map_sum, ha]
    exact hf
  have hg' : (∑ i, (g (star (a i) * a i)).re) ≤ 1 := by
    rw [← Complex.re_sum, ← map_sum, ha]
    exact hg
  calc
    _ ≤ ∑ i, M ^ 4 * ‖ξ‖ ^ 2 *
        ((f (star (a i) * a i)).re + (g (star (a i) * a i)).re) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [star_star] using hfg (star (a i))
    _ = M ^ 4 * ‖ξ‖ ^ 2 *
        ((∑ i, (f (star (a i) * a i)).re) + ∑ i, (g (star (a i) * a i)).re) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ M ^ 4 * ‖ξ‖ ^ 2 * (1 + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hf' hg') (by positivity)
    _ = _ := by ring

theorem normalized_orbit_sum_le (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ∑ i, ‖π.1 (a i) ξ‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
  have h := normalized_adjoint_orbit_sum_le (sharpHom π) hM (sharpHom_bound π hπ) a ha ξ
  simpa only [sharpHom_apply, ← ContinuousLinearMap.star_eq_adjoint, star_star] using h

theorem norm_sq_le_normalized_orbit_sum (π : BoundedUnitalHom A H)
    {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ a, ‖π.1 a‖ ≤ M * ‖a‖)
    {n : ℕ} (a : Fin n → A) (ha : ∑ i, star (a i) * a i = 1) (ξ : H) :
    ‖ξ‖ ^ 2 ≤ (2 * M ^ 4) * ∑ i, ‖π.1 (a i) ξ‖ ^ 2 := by
  let U : HilbertCopies H n := WithLp.toLp 2 (fun i => (π.1 (star (a i))).adjoint ξ)
  let V : HilbertCopies H n := WithLp.toLp 2 (fun i => π.1 (a i) ξ)
  have hidentity : ∑ i, π.1 (star (a i)) (π.1 (a i) ξ) = ξ := by
    have h := congrArg (fun b : A => π.1 b ξ) ha
    simpa only [map_sum, map_mul, map_one, sum_apply, mul_apply_eq_comp, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply] using h
  have hinner : inner ℂ U V = (‖ξ‖ ^ 2 : ℝ) := by
    simp only [PiLp.inner_apply, U, V,
      ContinuousLinearMap.adjoint_inner_left, ← inner_sum, hidentity,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hnorm : ‖ξ‖ ^ 2 ≤ ‖U‖ * ‖V‖ := by
    simpa only [hinner, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] using
      norm_inner_le_norm (𝕜 := ℂ) U V
  have hu : ‖U‖ ^ 2 ≤ 2 * M ^ 4 * ‖ξ‖ ^ 2 := by
    simpa only [PiLp.norm_sq_eq_of_L2, U, WithLp.ofLp_toLp] using
      normalized_adjoint_orbit_sum_le π hM hπ a ha ξ
  have hv : ‖V‖ ^ 2 = ∑ i, ‖π.1 (a i) ξ‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, V]
  have hs := pow_le_pow_left₀ (sq_nonneg ‖ξ‖) hnorm 2
  rw [mul_pow] at hs
  have hs' := mul_le_mul_of_nonneg_right hu (sq_nonneg ‖V‖)
  rw [hv] at hs hs'
  by_cases hz : ξ = 0
  · simp [hz]
  · have hp : 0 < ‖ξ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith

end KadisonSimilarity

end

end OAI
