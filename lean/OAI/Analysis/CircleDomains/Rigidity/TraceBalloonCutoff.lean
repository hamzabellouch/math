import OAI.Analysis.CircleDomains.Topology.CenteredSmallCutoffs

namespace OAI

/-! Smooth radial balloon cutoffs with one scale-independent derivative
constant for each fixed inner-radius ratio. Their derivatives vanish
outside the open outer balloon, not just outside its closure. -/
open Set Function Filter Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

 theorem exists_trace_balloon_cutoffs {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℂ, ∀ d : ℝ, 0 < d →
      ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧
        (∀ z, f z ∈ Icc (0:ℝ) 1) ∧
        (∀ z, ‖z-c‖ ≤ α*d → f z = 0) ∧
        (∀ z, d ≤ ‖z-c‖ → f z = 1) ∧
        (∀ z, ‖fderiv ℝ f z‖ ≤ (ball c d).indicator (fun _ => C/d) z) := by
  let β := (α+1)/2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  let ψ : ContDiffBump (0 : ℂ) := ⟨α,β,hα,hαβ⟩
  have hψ : ContDiff ℝ ∞ (ψ : ℂ → ℝ) := ψ.contDiff
  have hdψ : Continuous (fderiv ℝ (ψ : ℂ → ℝ)) :=
    (hψ.fderiv_right (m := (↑(⊤ : ℕ∞))) (by simp)).continuous
  obtain ⟨D,hD⟩ := hdψ.norm.bounded_above_of_compact_support
    ((ψ.hasCompactSupport.fderiv (𝕜 := ℝ)).norm)
  let C := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDbound (z : ℂ) : ‖fderiv ℝ (ψ : ℂ → ℝ) z‖ ≤ C := by
    have hh : ‖fderiv ℝ (ψ : ℂ → ℝ) z‖ ≤ D := by simpa only [norm_norm] using hD z
    exact hh.trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro c d hd
  let φ := translatedCutoff (dilatedCutoff ψ d) c
  let f := fun z => 1-φ z
  have hφ : ContDiff ℝ ∞ φ :=
    (dilatedCutoff_smooth hψ d).comp (contDiff_id.sub contDiff_const)
  have he (z : ℂ) : φ z = ψ (d⁻¹ • (z-c)) := rfl
  have hder (z : ℂ) : fderiv ℝ f z = -(d⁻¹ • fderiv ℝ (ψ : ℂ → ℝ) (d⁻¹ • (z-c))) := by
    rw [show f = (fun z => 1-φ z) from rfl,fderiv_const_sub,
      translatedCutoff_fderiv ((dilatedCutoff_smooth hψ d).differentiable (by simp)),
      dilatedCutoff_fderiv (hψ.differentiable (by simp))]
  have hn (z : ℂ) : ‖d⁻¹ • (z-c)‖ = ‖z-c‖/d := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
    ring
  refine ⟨f,contDiff_const.sub hφ,?_,?_,?_,?_⟩
  · intro z
    change 1-φ z ∈ Icc (0:ℝ) 1
    rw [he]
    exact ⟨sub_nonneg.mpr ψ.le_one,sub_le_self _ ψ.nonneg⟩
  · intro z hz
    have hx : d⁻¹ • (z-c) ∈ closedBall (0 : ℂ) ψ.rIn := by
      rw [mem_closedBall,dist_zero_right,hn]
      exact (div_le_iff₀ hd).mpr hz
    change 1-φ z = 0
    rw [he,ψ.one_of_mem_closedBall hx,sub_self]
  · intro z hz
    have hx : ψ.rOut ≤ dist (d⁻¹ • (z-c)) (0 : ℂ) := by
      rw [dist_zero_right,hn]
      exact hβ1.le.trans ((one_le_div hd).mpr hz)
    change 1-φ z = 1
    rw [he,ψ.zero_of_le_dist hx,sub_zero]
  · intro z
    by_cases hz : z ∈ ball c d
    · rw [indicator_of_mem hz _,hder,norm_neg,norm_smul,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hd)]
      simpa only [div_eq_mul_inv,mul_comm] using
        mul_le_mul_of_nonneg_left (hDbound (d⁻¹ • (z-c))) (inv_nonneg.mpr hd.le)
    · have hdist : d ≤ ‖z-c‖ := by simpa only [mem_ball,dist_eq_norm,not_lt] using hz
      have hzero : fderiv ℝ (ψ : ℂ → ℝ) (d⁻¹ • (z-c)) = 0 := by
        by_contra hne
        have hx := support_fderiv_subset ℝ hne
        rw [ψ.tsupport_eq,mem_closedBall,dist_zero_right,hn] at hx
        have hl : 1 ≤ ‖z-c‖/d := (one_le_div hd).mpr hdist
        exact (not_le_of_gt hβ1) (hl.trans hx)
      rw [indicator_of_notMem hz _,hder,hzero,smul_zero,neg_zero,norm_zero]

end CircleDomainRigidity

end

end OAI
