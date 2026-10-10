import OAI.Probability.FreeIsing.Trees.ColoredPathCount

namespace OAI

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem367.ColoredPathAverage
open ColoredEdgeLifts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [CompleteSpace E] {d : ℕ}

theorem inner_forwardOperator_pow_component_eq (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E)
    (i : Fin d) (c : ℝ)
    (h : ∀ p : Path d n i, inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ (f i)
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f i) = c := by
  rw [forwardOperator_pow_apply, inner_smul_right, inner_sum]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_path]
  have hd1 : 1 ≤ d := by omega
  have hb : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  rw [Nat.cast_pow, Nat.cast_sub hd1, Nat.cast_one, ← mul_assoc,
    ← mul_pow, inv_mul_cancel₀ hb, one_pow, one_mul]

theorem inner_forwardOperator_pow_eq_card_mul (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c) :
    inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f) =
        (d : ℝ) * c := by
  rw [PiLp.inner_apply]
  simp only [inner_forwardOperator_pow_component_eq hd S n f _ c (h _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem abs_pathCoefficient_le (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c B : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hB : |inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f)| ≤
        (d : ℝ) * B) : |c| ≤ B := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  rw [inner_forwardOperator_pow_eq_card_mul hd S n f c h,
    abs_mul, abs_of_pos hdreal] at hB
  exact (mul_le_mul_iff_right₀ hdreal).mp hB

theorem abs_pathCoefficient_le_norm_pow (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (n : ℕ) (f : EdgeSpace d E) (c V : ℝ)
    (h : ∀ (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c)
    (hsize : ‖f‖ ^ 2 ≤ (d : ℝ) * V) :
    |c| ≤ ‖forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n‖ * V := by
  apply abs_pathCoefficient_le hd S n f c _ h
  let A := forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n
  change |inner ℝ f (A f)| ≤ (d : ℝ) * (‖A‖ * V)
  calc
    |inner ℝ f (A f)| ≤ ‖f‖ * ‖A f‖ := by
      simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) f (A f)
    _ ≤ ‖f‖ * (‖A‖ * ‖f‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm f) (norm_nonneg f)
    _ = ‖A‖ * ‖f‖ ^ 2 := by ring
    _ ≤ ‖A‖ * ((d : ℝ) * V) :=
      mul_le_mul_of_nonneg_left hsize (norm_nonneg A)
    _ = _ := by ring

theorem summable_pathCoefficients (hd : 2 ≤ d)
    (S : Fin d → E ≃ₗᵢ[ℝ] E) (f : EdgeSpace d E) (c : ℕ → ℝ)
    (h : ∀ (n : ℕ) (i : Fin d) (p : Path d n i),
      inner ℝ (f i) (pathValue S f p) = c n)
    (hsum : Summable (fun n : ℕ => |inner ℝ f
      ((forwardOperator (by omega : 0 < d) S ((d : ℝ) - 1)⁻¹ ^ n) f)|)) :
    Summable (fun n => |c n|) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : Summable (fun n => (d : ℝ) * |c n|) := by
    simpa only [inner_forwardOperator_pow_eq_card_mul hd S _ f _ (h _),
      abs_mul, abs_of_pos hdreal] using hsum
  exact (summable_mul_left_iff hdreal.ne').mp hs

end Problem367.ColoredPathAverage

end

end OAI
