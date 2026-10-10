import OAI.Combinatorics.MatchingPSD.FiberAverages

namespace OAI

namespace MatchingSmoothing
open Filter Asymptotics

lemma eventually_power_le_choose (m k : ℕ) (hm : m < k) (c : ℝ) :
    ∀ᶠ h : ℕ in atTop, c * (h : ℝ)^m ≤ (h.choose k : ℝ) := by
  have ho : (fun h : ℕ => (h : ℝ)^m) =o[atTop] (fun h : ℕ => (h : ℝ)^k) :=
    (isLittleO_pow_pow_atTop_of_lt hm).comp_tendsto tendsto_natCast_atTop_atTop
  have hb := ((ho.const_mul_left c).trans_isBigO (isTheta_choose k).symm.isBigO).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hb] with h hh
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ h.choose k by positivity), one_mul] using hh)

lemma eventually_table_moment_small (K : ℕ) :
    ∀ᶠ h : ℕ in atTop, 4*(4*K+34) < h ∧
      (h+1 : ℝ)^33 ≤ (h.choose (4*K+34) : ℝ) * ((2*h : ℝ)^(2*K))⁻¹^2 := by
  have hb := eventually_power_le_choose (33+4*K) (4*K+34) (by omega)
    ((2 : ℝ)^(33+4*K))
  filter_upwards [hb, eventually_gt_atTop (4*(4*K+34))] with h hh hk
  refine ⟨hk, ?_⟩
  have hp : (0 : ℝ) < 2*h := by
    have : 0 < h := by omega
    positivity
  have h1 : (1 : ℝ) ≤ h := by exact_mod_cast (show 1 ≤ h by omega)
  rw [inv_pow, le_mul_inv_iff₀ (pow_pos (pow_pos hp _) _)]
  calc
    (h+1 : ℝ)^33 * ((2*h : ℝ)^(2*K))^2 ≤
        (2*h : ℝ)^33 * ((2*h : ℝ)^(2*K))^2 := by gcongr; linarith
    _ = (2*h : ℝ)^(33+4*K) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ ≤ (h.choose (4*K+34) : ℝ) := by simpa only [mul_pow] using hh

noncomputable def polynomialProjection (h d : ℕ) (f : MatchingSpace h) : MatchingSpace h :=
  (polynomialSpace h d).starProjection f

lemma residual_mem_high (h d : ℕ) (f : MatchingSpace h) :
    f - polynomialProjection h d f ∈ (polynomialSpace h d)ᗮ := by
  exact (polynomialSpace h d).sub_starProjection_mem_orthogonal f

lemma residual_norm_le (h d : ℕ) (f : MatchingSpace h) :
    ‖f - polynomialProjection h d f‖ ≤ ‖f‖ := by
  rw [polynomialProjection, ← Submodule.starProjection_orthogonal_val]
  exact (polynomialSpace h d)ᗮ.norm_starProjection_apply_le f

lemma uniform_table_smoothing (K : ℕ) :
    ∃ d H : ℕ, 0 < d ∧ ∀ h : ℕ, H ≤ h →
      ∀ (f₀ : Vertices h → Fin 3), (∀ i, 0 < histogram f₀ i) →
      ∀ f : MatchingSpace h,
      (∑ z, fiberAverage (tableRelation f₀)
        (matchingEquiv h (f - polynomialProjection h d f)) z ^ 2) /
        Fintype.card (Colorings (Vertices h) (Fin 3) (histogram f₀)) ≤
      ((2*h : ℝ)^(2*K))⁻¹ *
        ((∑ M, (f M)^2) / Fintype.card (Pairing (Vertices h))) := by
  obtain ⟨H, hH⟩ := eventually_atTop.mp (eventually_table_moment_small K)
  let k := 4*K+34
  let d := (4*k)*(4*k)
  refine ⟨d, H, by dsimp [d, k]; positivity, ?_⟩
  intro h hh f₀ hf₀ f
  obtain ⟨hk, hb⟩ := hH h hh
  apply (table_smoothing_bound k hk f₀ hf₀ _ (by positivity) hb
    _ (residual_mem_high h d f)).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq]
  exact pow_le_pow_left₀ (norm_nonneg _) (residual_norm_le h d f) _

end MatchingSmoothing

end OAI
