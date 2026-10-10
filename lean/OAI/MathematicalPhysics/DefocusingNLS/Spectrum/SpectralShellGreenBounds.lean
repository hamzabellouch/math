import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! The two action factors in the scalar Green kernel stay in their own channel.
No comparison between the actions of distinct channels is needed. -/

namespace DefocusingNLS

private theorem action_ratio (C c k H A B : ℝ)
    (hc : c≠0) (hk : k≠0) :
    (C*Real.exp A/k)/(c*Real.exp H)*(C*Real.exp (H-B))=
      C^2/(c*k)*Real.exp (A-B) := by
  have he : Real.exp A*Real.exp (H-B)=Real.exp H*Real.exp (A-B) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  field_simp
  linear_combination C^2*he

theorem spectralShellNorm_green_factor (kr kt C c HR Hr Ht : ℝ)
    (hkr : 0≤ kr) (hkt : 0<kt) (hC : 0≤ C) (hc : 0<c)
    (D U : ℂ × ℂ) (W : ℂ)
    (hD : spectralShellNorm kr D≤ C*Real.exp (HR-Hr))
    (hU : spectralShellNorm kt U≤ C*Real.exp Ht)
    (hW : c*Real.exp HR≤‖W‖) :
    spectralShellNorm kr ((U.1/W) • D)≤ C^2/(c*kt)*Real.exp (Ht-Hr) := by
  have hw : 0<‖W‖ := lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hW
  have hD0 := spectralShellNorm_nonneg kr hkr D
  have hU0 := spectralShellNorm_nonneg kt hkt.le U
  have hv := spectralShellNorm_value kt hkt U
  rw [spectralShellNorm_smul,norm_div]
  calc
    _ ≤ (spectralShellNorm kt U/kt)/‖W‖*spectralShellNorm kr D := by
      gcongr
    _ ≤ (C*Real.exp Ht/kt)/(c*Real.exp HR)*(C*Real.exp (HR-Hr)) := by
      gcongr
    _ = _ := action_ratio C c kt HR Ht Hr hc.ne' hkt.ne'

theorem spectralScalarGreenState_shell_bound
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (k H : ℝ → ℝ)
    (C c HR r t : ℝ) (hC : 0≤ C) (hc : 0<c)
    (hkr : 0<k r) (hkt : 0<k t)
    (hD : ∀ s ∈ ({r,t} : Set ℝ), spectralShellNorm (k s) (D s)≤ C*Real.exp (HR-H s))
    (hU : ∀ s ∈ ({r,t} : Set ℝ), spectralShellNorm (k s) (U s)≤ C*Real.exp (H s))
    (hW : c*Real.exp HR≤‖W‖)
    (hH : AntitoneOn H (Set.Icc (min r t) (max r t))) :
    spectralShellNorm (k r) (spectralScalarGreenState D U W r t)≤ C^2/(c*k t) := by
  have hrmem : r ∈ Set.Icc (min r t) (max r t) := ⟨min_le_left _ _,le_max_left _ _⟩
  have htmem : t ∈ Set.Icc (min r t) (max r t) := ⟨min_le_right _ _,le_max_right _ _⟩
  have hrr : r ∈ ({r,t} : Set ℝ) := by simp only [Set.mem_insert_iff,true_or]
  have htt : t ∈ ({r,t} : Set ℝ) := by simp only [Set.mem_insert_iff,Set.mem_singleton_iff,or_true]
  have hconst : 0≤ C^2/(c*k t) := by positivity
  by_cases hrt : r≤ t
  · rw [spectralScalarGreenState,ite_eq_left hrt]
    apply (spectralShellNorm_green_factor (k r) (k t) C c HR (H r) (H t)
      hkr.le hkt hC hc (D r) (U t) W (hD r hrr) (hU t htt) hW).trans
    calc
      _ ≤ C^2/(c*k t)*1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hH hrmem htmem hrt))) hconst
      _ = _ := mul_one _
  · rw [spectralScalarGreenState,ite_eq_right hrt]
    have hb := spectralShellNorm_green_factor (k r) (k t) C c HR
      (HR-H r) (HR-H t) hkr.le hkt hC hc (U r) (D t) W
      (by simpa only [sub_sub_cancel] using hU r hrr) (hD t htt) hW
    have he : (HR-H t)-(HR-H r)=H r-H t := by ring
    rw [he] at hb
    apply hb.trans
    calc
      _ ≤ C^2/(c*k t)*1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hH htmem hrmem (le_of_not_ge hrt)))) hconst
      _ = _ := mul_one _

end DefocusingNLS

end OAI
