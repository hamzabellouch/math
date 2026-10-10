import Mathlib
import OAI.Analysis.SymmetricDomains.NormalScaleBound

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Asymptotics
open scoped Topology

theorem log_near_one_bound : ∃ A > 0, ∀ᶠ z : ℂ in 𝓝 1,
    z ≠ 0 ∧ ‖Complex.log z‖ ≤ A*‖z-1‖ := by
  obtain ⟨A,hA,ha⟩ := (Complex.differentiableAt_log Complex.one_mem_slitPlane).isBigO_sub.exists_pos
  refine ⟨A,hA,?_⟩
  filter_upwards [ha.bound, isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0)] with z hz hne
  exact ⟨hne,by simpa only [Complex.log_one,sub_zero] using hz⟩

theorem independent_support_coercivity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    (β : Fin (k+1) → Fin (k+1) → ℝ) (hβ : LinearIndependent ℝ β)
    (h : Fin (k+1) → E × (Fin (k+1) → ℂ) → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) 0) (hh0 : ∀ i, h i 0 = 1)
    (hder : ∀ i x, fderiv ℂ (fun y => Complex.log (h i y)) 0 x =
      Complex.I*∑ j, (β i j : ℂ)*x.2 j)
    (D : Set (E × (Fin (k+1) → ℂ))) {c : ℝ} (hc : 0 < c)
    (hpeak : ∀ x ∈ D, ‖h 0 x‖ ≤ Real.exp (-c*‖x‖^2)) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin (k+1) → ℂ)), ∀ x ∈ V, x ∈ D →
      ‖x‖^2 ≤ C*‖fun i => 1-h i x‖ ∧ ‖x.2‖ ≤ C*‖fun i => 1-h i x‖ := by
  classical
  obtain ⟨A,hA,hlog⟩ := log_near_one_bound
  have he : ∀ᶠ x in 𝓝 (0 : E × (Fin (k+1) → ℂ)), ∀ i,
      h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖ := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hh0 i) ▸ (hh i).continuousAt.tendsto) hlog
  have hal : ∀ i, AnalyticAt ℂ (fun x => Complex.log (h i x)) 0 :=
    fun i => (hh i).clog (by rw [hh0]; exact Complex.one_mem_slitPlane)
  obtain ⟨B,hB,W,hW,hscale⟩ := normal_scale_bound β hβ
    (fun i x => Complex.log (h i x)) hal (by simp [hh0]) hder
  refine ⟨max (A/c) (B*(A+A/c)), lt_of_lt_of_le (div_pos hA hc) (le_max_left _ _),
    W ∩ {x | ∀ i, h i x ≠ 0 ∧ ‖Complex.log (h i x)‖ ≤ A*‖h i x-1‖},
    inter_mem hW he,?_⟩
  intro x hx hxD
  let d := ‖fun i => (1 : ℂ)-h i x‖
  have hd : 0 ≤ d := norm_nonneg _
  have hld : ‖fun i => Complex.log (h i x)‖ ≤ A*d := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hA.le hd)).mpr
    intro i
    calc
      _ ≤ A*‖h i x-1‖ := (hx.2 i).2
      _ = A*‖1-h i x‖ := by rw [norm_sub_rev]
      _ ≤ A*d := mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => (1 : ℂ)-h i x) i) hA.le
  have hreal : (Complex.log (h 0 x)).re ≤ -c*‖x‖^2 := by
    rw [Complex.log_re]
    exact (Real.log_le_iff_le_exp (norm_pos_iff.mpr (hx.2 0).1)).mpr (hpeak x hxD)
  have hs : ‖x‖^2 ≤ (A/c)*d := by
    have hr := Complex.abs_re_le_norm (Complex.log (h 0 x))
    have hnorm : ‖Complex.log (h 0 x)‖ ≤ A*d :=
      (norm_le_pi_norm (fun i => Complex.log (h i x)) 0).trans hld
    have hh' : c*‖x‖^2 ≤ A*d := by
      have habs := neg_le_abs (Complex.log (h 0 x)).re
      linarith
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hh']
  constructor
  · exact hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hd)
  · calc
      ‖x.2‖ ≤ B*(‖fun i => Complex.log (h i x)‖+‖x‖^2) := hscale x hx.1
      _ ≤ B*(A*d+(A/c)*d) := mul_le_mul_of_nonneg_left (add_le_add hld hs) hB.le
      _ = (B*(A+A/c))*d := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hd

end Release061

end

end OAI
