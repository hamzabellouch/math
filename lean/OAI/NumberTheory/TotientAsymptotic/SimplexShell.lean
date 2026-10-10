import OAI.NumberTheory.TotientAsymptotic.SimplexVolume

namespace OAI

/-! Explicit slack-shell bounds for the prefix simplexes. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma pow_sub_positivePart_le {T w : ℝ} (hT : 0 ≤ T) (hw : 0 ≤ w) (N : ℕ) :
    T^N-(max (T-w) 0)^N ≤ w*N*T^(N-1) := by
  have hb0 : 0 ≤ max (T-w) 0 := le_max_right _ _
  have hbT : max (T-w) 0 ≤ T := max_le (by linarith) hT
  have hdiff : 0 ≤ T^N-(max (T-w) 0)^N :=
    sub_nonneg.mpr (pow_le_pow_left₀ hb0 hbT N)
  have hh := abs_pow_sub_pow_le (a := T) (b := max (T-w) 0) (n := N)
  rw [abs_of_nonneg hdiff, abs_of_nonneg (sub_nonneg.mpr hbT),
    abs_of_nonneg hT, abs_of_nonneg hb0, max_eq_left hbT] at hh
  apply hh.trans
  have hgap : T-max (T-w) 0 ≤ w := by linarith [le_max_left (T-w) 0]
  gcongr

def raiseThreshold {N : ℕ} (C : Fin N → ℝ) (i : Fin N) (t : ℝ) : Fin N → ℝ :=
  Function.update C i (C i+t)

lemma weighted_raiseThreshold {N : ℕ} (C : Fin N → ℝ) (i : Fin N) (t : ℝ) :
    (∑ j, g (j.val+1)*raiseThreshold C i t j) =
      (∑ j, g (j.val+1)*C j)+g (i.val+1)*t := by
  classical
  have he (j : Fin N) : g (j.val+1)*raiseThreshold C i t j =
      g (j.val+1)*C j + if j=i then g (i.val+1)*t else 0 := by
    by_cases hji : j=i
    · subst j
      simp [raiseThreshold, mul_add]
    · simp [raiseThreshold, hji]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

lemma raised_region_subset {N : ℕ} (B C₀ : ℝ) (C : Fin N → ℝ)
    (i : Fin N) {t : ℝ} (ht : 0 ≤ t) :
    prefixRegion N B C₀ (raiseThreshold C i t) ⊆ prefixRegion N B C₀ C := by
  intro u hu
  refine ⟨fun j => ?_, hu.2⟩
  have hj := hu.1 j
  by_cases hji : j=i
  · subst j
    simp only [raiseThreshold, Function.update_self] at hj
    linarith
  · simpa [raiseThreshold, hji] using hj

lemma measurableSet_prefixRegion (N : ℕ) (B C₀ : ℝ) (C : Fin N → ℝ) :
    MeasurableSet (prefixRegion N B C₀ C) := by
  rw [prefixRegion_eq_simplex_preimage]
  exact (prefixAffine_preserves_volume _ _).measurable (measurableSet_weightedSimplex _ _)

/-- Removing a band of thickness `t` in one slack coordinate loses at most
its slice coefficient times `t`. This holds with every fixed tail threshold. -/
theorem prefix_slack_shell_bound {N : ℕ} (hN : 0 < N)
    (B C₀ : ℝ) (C : Fin N → ℝ) (i : Fin N) {t : ℝ} (ht : 0 ≤ t)
    (hT : 0 ≤ B-C₀-∑ j, g (j.val+1)*C j) :
    (volume (prefixRegion N B C₀ C \ prefixRegion N B C₀ (raiseThreshold C i t))).toReal ≤
      (t*N*g (i.val+1)*(B-C₀-∑ j, g (j.val+1)*C j)^(N-1)) /
        ((N.factorial : ℝ)*∏ j : Fin N, g (j.val+1)) := by
  have hden : 0 < (N.factorial : ℝ)*∏ j : Fin N, g (j.val+1) :=
    mul_pos (by positivity) (Finset.prod_pos (fun j _ => g_pos _))
  have hfinite : volume (prefixRegion N B C₀ C) ≠ ⊤ := by
    rw [volume_prefixRegion_explicit _ hN]
    exact ENNReal.ofReal_ne_top
  change volume.real _ ≤ _
  rw [measureReal_sdiff (raised_region_subset B C₀ C i ht)
    (measurableSet_prefixRegion _ _ _ _) hfinite]
  change (volume (prefixRegion N B C₀ C)).toReal-
    (volume (prefixRegion N B C₀ (raiseThreshold C i t))).toReal ≤ _
  rw [volume_prefixRegion_explicit _ hN, volume_prefixRegion_explicit _ hN,
    weighted_raiseThreshold, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), max_eq_left hT, ← sub_div]
  apply (div_le_div_iff_of_pos_right hden).mpr
  have hh := pow_sub_positivePart_le hT (mul_nonneg (g_pos (i.val+1)).le ht) N
  convert hh using 1 <;> ring_nf

end TotientAsymptotic

end

end OAI
