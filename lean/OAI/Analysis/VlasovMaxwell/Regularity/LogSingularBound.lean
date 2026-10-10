import Mathlib

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma singular_radial_split_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t θ A N : ℝ} (hθ : 0<θ) (hθt : θ≤t)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      ‖∫r in Ioc (0:ℝ) t,g r‖≤N*θ+A*Real.log (t/θ) := by
  have ht : 0<t := hθ.trans_le hθt
  have hi : IntegrableOn g (Ioc (0:ℝ) t) :=
    (integrableOn_const (μ:=volume) (s:=Ioc (0:ℝ) t) (C:=N) measure_Ioc_lt_top.ne).mono'
      (hg.aestronglyMeasurable measurableSet_Ioc) (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hn r hr)
  have hi₁ : IntervalIntegrable g volume 0 θ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθ.le).mpr
      (hi.mono_set (Ioc_subset_Ioc_right hθt))
  have hi₂ : IntervalIntegrable g volume θ t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hθt).mpr
      (hi.mono_set (Ioc_subset_Ioc_left hθ.le))
  have h₁ : ‖∫r in (0:ℝ)..θ,g r‖≤N*θ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (f:=g) (a:=0) (b:=θ) (C:=N) (by
      rw [uIoc_of_le hθ.le]
      intro r hr
      exact hn r ⟨hr.1,hr.2.trans hθt⟩)
    simpa only [sub_zero,abs_of_pos hθ] using hh
  have hci : IntervalIntegrable (fun r : ℝ => A/r) volume θ t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hθt]
    exact continuousOn_const.div continuousOn_id (fun r hr => (hθ.trans_le hr.1).ne')
  have h₂ : ‖∫r in θ..t,g r‖≤A*Real.log (t/θ) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le (f:=g) hθt (by
      filter_upwards [] with r hr
      exact ha r ⟨hθ.trans hr.1,hr.2⟩) hci
    apply hh.trans_eq
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul,integral_inv_of_pos hθ ht]
    simp only [div_eq_mul_inv]
  refine ⟨hi,?_⟩
  rw [←intervalIntegral.integral_of_le ht.le,←intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

lemma singular_radial_log_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g : ℝ → W} {t H A N : ℝ} (ht : 0<t) (htH : t≤H) (hA : 0≤A) (hN : 0≤N)
    (hg : ContinuousOn g (Ioc (0:ℝ) t))
    (hn : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤N)
    (ha : ∀ r∈Ioc (0:ℝ) t, ‖g r‖≤A/r) :
    IntegrableOn g (Ioc (0:ℝ) t) ∧
      ‖∫r in Ioc (0:ℝ) t,g r‖≤1+A*(Real.log (max 1 H)+Real.log (1+N)) := by
  let θ := min t (1+N)⁻¹
  have hp : 0<1+N := by linarith
  have hθ : 0<θ := lt_min ht (inv_pos.mpr hp)
  obtain ⟨hi,hb⟩ := singular_radial_split_bound hθ (min_le_left _ _) hg hn ha
  refine ⟨hi,hb.trans ?_⟩
  have hnear : N*θ≤1 := by
    calc
      N*θ≤N*(1+N)⁻¹ := mul_le_mul_of_nonneg_left (min_le_right _ _) hN
      _ ≤ 1 := by rw [←div_eq_mul_inv]; exact (div_le_one hp).mpr (by linarith)
  have hratio : t/θ≤(max 1 H)*(1+N) := by
    by_cases hh : t≤(1+N)⁻¹
    · simp only [θ,min_eq_left hh,div_self ht.ne']
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (by linarith)
    · rw [show θ=(1+N)⁻¹ from min_eq_right (le_of_not_ge hh),div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_right (htH.trans (le_max_right _ _)) hp.le
  have hl : Real.log (t/θ)≤Real.log (max 1 H)+Real.log (1+N) := by
    calc
      Real.log (t/θ)≤Real.log (max 1 H*(1+N)) := Real.log_le_log (div_pos ht hθ) hratio
      _ = _ := Real.log_mul (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _))) hp.ne'
  exact add_le_add hnear (mul_le_mul_of_nonneg_left hl hA)

end RVM
end

end OAI
