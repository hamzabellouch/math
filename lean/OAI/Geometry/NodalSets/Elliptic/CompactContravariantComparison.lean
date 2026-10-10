import OAI.Geometry.NodalSets.Elliptic.PositiveContravariant
import OAI.Geometry.NodalSets.Elliptic.UniformContact

namespace OAI

namespace Yau.Geometry
open Set Yau.Jets
noncomputable section
variable {T E : Type*} [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_contravariant_margin (c : T → CoefficientPoint E) (hc : Continuous c)
    (hp : ∀ t (alpha : E →L[ℝ] ℝ), alpha ≠ 0 → 0 < alpha ((c t).1 alpha))
    (hr : ∀ t, 0 < (c t).2) :
    ∃ m > 0, (∀ t (alpha : E →L[ℝ] ℝ), m*‖alpha‖^2 ≤ alpha ((c t).1 alpha)) ∧ ∀ t, m ≤ (c t).2 := by
  have hcont : Continuous (fun z : T × (E →L[ℝ] ℝ) ↦ z.2 ((c z.1).1 z.2)) :=
    continuous_snd.clm_apply ((hc.fst.comp continuous_fst).clm_apply continuous_snd)
  obtain ⟨a,ha,_,_,hbound⟩ := compact_positive_bounds
    (isCompact_univ.prod (isCompact_sphere (0 : E →L[ℝ] ℝ) 1)) _ hcont.continuousOn
    (fun z hz ↦ hp z.1 z.2 (by intro he; simpa [he] using hz.2))
  have hco (t : T) (alpha : E →L[ℝ] ℝ) : a*‖alpha‖^2 ≤ alpha ((c t).1 alpha) := by
    by_cases hz : alpha=0
    · simp [hz]
    have hn : 0 < ‖alpha‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖alpha‖⁻¹:ℝ) • alpha‖=1 := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
    have hh := (hbound (t,(‖alpha‖⁻¹:ℝ) • alpha)
      ⟨mem_univ _,by simpa only [Metric.mem_sphere,dist_zero_right] using hu⟩).1
    simp only [map_smul,smul_apply,smul_eq_mul] at hh
    have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg ‖alpha‖)
    have he : ‖alpha‖^2*(‖alpha‖⁻¹*(‖alpha‖⁻¹*alpha ((c t).1 alpha))) =
        alpha ((c t).1 alpha) := by field_simp
    rw [he] at hmul
    nlinarith
  obtain ⟨b,hb,_,_,hbr⟩ := compact_positive_bounds isCompact_univ _ hc.snd.continuousOn
    (fun t _ ↦ hr t)
  exact ⟨min a b,lt_min ha hb,
    fun t alpha ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg ‖alpha‖)).trans (hco t alpha),
    fun t ↦ (min_le_right _ _).trans (hbr t (mem_univ t)).1⟩

omit [FiniteDimensional ℝ E] in
lemma coefficient_relative_comparison (c d : CoefficientPoint E) {m eps : ℝ}
    (_hm : 0 < m) (heps : 0 ≤ eps)
    (hc : ∀ alpha : E →L[ℝ] ℝ, m*‖alpha‖^2 ≤ alpha (c.1 alpha)) (hr : m ≤ c.2)
    (hd : ‖d-c‖ ≤ eps*m) :
    (∀ alpha : E →L[ℝ] ℝ, |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ eps*alpha (c.1 alpha)) ∧
    |d.2-c.2| ≤ eps*c.2 := by
  have hop : ‖d.1-c.1‖ ≤ eps*m := (norm_fst_le (d-c)).trans hd
  constructor
  · intro alpha
    have hn : |alpha (d.1 alpha)-alpha (c.1 alpha)| ≤ ‖d.1-c.1‖*‖alpha‖^2 := by
      calc
        _ = ‖alpha ((d.1-c.1) alpha)‖ := by rw [sub_apply,map_sub,Real.norm_eq_abs]
        _ ≤ ‖alpha‖*‖(d.1-c.1) alpha‖ := alpha.le_opNorm _
        _ ≤ ‖alpha‖*(‖d.1-c.1‖*‖alpha‖) :=
          mul_le_mul_of_nonneg_left ((d.1-c.1).le_opNorm alpha) (norm_nonneg alpha)
        _ = _ := by ring
    exact hn.trans ((mul_le_mul_of_nonneg_right hop (sq_nonneg ‖alpha‖)).trans
      (by nlinarith [mul_le_mul_of_nonneg_left (hc alpha) heps]))
  · exact (show |d.2-c.2| ≤ eps*m by
      have h := (norm_snd_le (d-c)).trans hd
      change ‖d.2-c.2‖ ≤ eps*m at h
      rwa [Real.norm_eq_abs] at h).trans
      (mul_le_mul_of_nonneg_left hr heps)

end
end Yau.Geometry

end OAI
