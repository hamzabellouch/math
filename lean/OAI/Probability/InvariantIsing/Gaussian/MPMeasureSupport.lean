import OAI.Probability.InvariantIsing.Gaussian.MPDensitySupport

namespace OAI

/-! The precise support and both endpoint clauses of the Gaussian MP input. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal Topology
namespace InvariantIsing

lemma mp_continuous_support_bound (α : ℝ) :
    ((volume.restrict (Icc (marchenkoPasturA α) (marchenkoPasturB α))).withDensity
      (fun x => ENNReal.ofReal (mpDensity α x))).support ⊆
        Icc (marchenkoPasturA α) (marchenkoPasturB α) := by
  apply (withDensity_absolutelyContinuous _ _).support_mono.trans
  exact (Measure.support_restrict_subset).trans fun _ hx => by
    simpa only [isClosed_Icc.closure_eq] using hx.1

theorem marchenkoPastur_support_bound {α : ℝ} (_hα : 0 < α) :
    (marchenkoPasturMeasure α).support ⊆ Icc (marchenkoPasturLower α) (marchenkoPasturB α) := by
  rw [marchenkoPasturMeasure_eq_density,Measure.support_add]
  by_cases ha : α ≤ 1
  · rw [marchenkoPasturLower,ite_eq_left ha]
    rintro x (hx|hx)
    · have hs : (ENNReal.ofReal (max (1-α) 0) • Measure.dirac (0 : ℝ)).support ⊆ {0} := by
        apply Measure.smul_absolutelyContinuous.support_mono.trans
        apply Measure.support_subset_of_isClosed isClosed_singleton
        rw [mem_ae_iff]
        simp
      have he : x = 0 := hs hx
      subst x
      exact ⟨le_rfl,sq_nonneg _⟩
    · exact ⟨(sq_nonneg (1-sqrt α)).trans (mp_continuous_support_bound α hx).1,
        (mp_continuous_support_bound α hx).2⟩
  · rw [marchenkoPasturLower,ite_eq_right ha]
    have hz : max (1-α) 0 = 0 := max_eq_right (by linarith)
    simpa only [hz,ENNReal.ofReal_zero,zero_smul,Measure.support_zero,empty_union] using
      mp_continuous_support_bound α

theorem marchenkoPastur_right_mem {α : ℝ} (hα : 0 < α) :
    marchenkoPasturB α ∈ (marchenkoPasturMeasure α).support :=
  mp_interval_subset_support hα ⟨(mp_edges_strict hα).le,le_rfl⟩

theorem marchenkoPastur_left_mem {α : ℝ} (hα : 0 < α) :
    marchenkoPasturLower α ∈ (marchenkoPasturMeasure α).support := by
  by_cases ha : α < 1
  · rw [marchenkoPasturLower,ite_eq_left ha.le]
    have hp : ENNReal.ofReal (max (1-α) 0) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (lt_max_of_lt_left (by linarith))).ne'
    have hac : Measure.dirac (0 : ℝ) ≪ marchenkoPasturMeasure α := by
      apply (Measure.absolutelyContinuous_smul hp).trans
      apply Measure.absolutelyContinuous_of_le
      rw [marchenkoPasturMeasure_eq_density]
      exact Measure.le_add_right le_rfl
    apply hac.support_mono
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hu : (0 : ℝ) ∈ U := mem_of_mem_nhds hU
    simp only [Measure.dirac_apply_of_mem hu,zero_lt_one]
  · have he : marchenkoPasturLower α = marchenkoPasturA α := by
      by_cases hle : α ≤ 1
      · have h : α = 1 := le_antisymm hle (not_lt.mp ha)
        subst α
        simp [marchenkoPasturLower,marchenkoPasturA]
      · simp only [marchenkoPasturLower,ite_eq_right hle]
    rw [he]
    exact mp_interval_subset_support hα ⟨le_rfl,(mp_edges_strict hα).le⟩

end InvariantIsing

end

end OAI
