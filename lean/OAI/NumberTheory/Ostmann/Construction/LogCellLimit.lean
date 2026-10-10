import OAI.NumberTheory.Ostmann.Construction.LogCellBounds

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace Ostmann.Construction

theorem tendsto_center_ratio (a : ℝ) :
    Tendsto (fun c : ℝ => c/(c+a)) atTop (𝓝 1) := by
  have hden : Tendsto (fun c : ℝ => c+a) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b-a)] with c hc
    linarith
  have hinv : Tendsto (fun c : ℝ => a/(c+a)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have h : Tendsto (fun c : ℝ => 1-a/(c+a)) atTop (𝓝 (1-0)) :=
    tendsto_const_nhds.sub hinv
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (-a)] with c hc
  have hn : c+a≠0 := ne_of_gt (by linarith)
  field_simp
  ring

theorem logCellMass_limit_of_logMass_limit
    (hW : Tendsto (fun c : ℝ => logCellLogMass c ∅) atTop (𝓝 1)) :
    Tendsto (fun c : ℝ => c*logCellMass c ∅) atTop (𝓝 1) := by
  have hlo : Tendsto (fun c : ℝ => c/(c+1)*logCellLogMass c ∅) atTop (𝓝 1) := by
    simpa only [mul_one] using (tendsto_center_ratio 1).mul hW
  have hhi : Tendsto (fun c : ℝ => c/(c-1)*logCellLogMass c ∅) atTop (𝓝 1) := by
    simpa only [mul_one, sub_eq_add_neg] using (tendsto_center_ratio (-1)).mul hW
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_order.mp hlo).1 (1-ε) (by linarith),
    (tendsto_order.mp hhi).2 (1+ε) (by linarith)] with c hc hl hu
  obtain ⟨hcl,hcu⟩ := center_mul_logCellMass_sandwich hc ∅
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem logCell_two_point_error_tendsto :
    Tendsto (fun c : ℝ => 2*c*Real.exp (1-c)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (2*Real.exp 1)
  simp only [mul_zero] at h
  convert h using 1
  funext c
  rw [sub_eq_add_neg, Real.exp_add, pow_one]
  ring

theorem logCellMass_limit_uniform_delete_two
    (hW : Tendsto (fun c : ℝ => logCellLogMass c ∅) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      |c*logCellMass c E-1|<ε := by
  intro ε hε
  have hmass := logCellMass_limit_of_logMass_limit hW
  have hhalf : 0<ε/2 := by linarith
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (Metric.tendsto_nhds.mp hmass) (ε/2) hhalf,
    (tendsto_order.mp logCell_two_point_error_tendsto).2 (ε/2) hhalf] with c hc hm he
  intro E hE
  obtain ⟨hd0,hd⟩ := logCellMass_delete_two c E hE
  have hscaled0 := mul_nonneg hc.le hd0
  have hscaled := mul_le_mul_of_nonneg_left hd hc.le
  rw [Real.dist_eq, abs_lt] at hm
  rw [abs_lt]
  constructor <;> nlinarith

theorem logCellLogMass_limit_uniform_delete_two
    (hW : Tendsto (fun c : ℝ => logCellLogMass c ∅) atTop (𝓝 1)) :
    ∀ ε : ℝ, 0<ε → ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      |logCellLogMass c E-1|<ε := by
  have hconst : Tendsto (fun c : ℝ => 2*Real.exp (1-c)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2*Real.exp 1)
    simp only [mul_zero] at h
    convert h using 1
    funext c
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have herror : Tendsto (fun c : ℝ => 2*(c+1)*Real.exp (1-c)) atTop (𝓝 0) := by
    have h := logCell_two_point_error_tendsto.add hconst
    simp only [add_zero] at h
    convert h using 1
    funext c
    ring
  intro ε hε
  have hhalf : 0<ε/2 := by linarith
  filter_upwards [eventually_ge_atTop (0:ℝ),
    (Metric.tendsto_nhds.mp hW) (ε/2) hhalf,
    (tendsto_order.mp herror).2 (ε/2) hhalf] with c hc hm he
  intro E hE
  obtain ⟨hd0,hd⟩ := logCellLogMass_delete_two hc E hE
  rw [Real.dist_eq, abs_lt] at hm
  rw [abs_lt]
  constructor <;> linarith

theorem logCellMass_eventually_normalizable
    (hW : Tendsto (fun c : ℝ => logCellLogMass c ∅) atTop (𝓝 1)) :
    ∀ᶠ c : ℝ in atTop, ∀ E : Finset ℕ, E.card≤2 →
      0<logCellMass c E ∧ c/2≤(logCellMass c E)⁻¹ ∧ (logCellMass c E)⁻¹≤2*c := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    logCellMass_limit_uniform_delete_two hW (1/2) (by norm_num)] with c hc hm
  intro E hE
  have he := abs_lt.mp (hm E hE)
  have hZ : 0<logCellMass c E := by
    apply (mul_pos_iff_of_pos_left hc).mp
    linarith
  refine ⟨hZ,?_,?_⟩
  · rw [inv_eq_one_div]
    apply (le_div_iff₀ hZ).mpr
    nlinarith
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hZ).mpr
    nlinarith

end Ostmann.Construction

end

end OAI
