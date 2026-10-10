import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGreenBounds

namespace OAI

/-! The outgoing normalization cancels between its value bound and the
Wronskian, so the Green bound is independent of the size of that solution. -/

namespace DefocusingNLS

theorem spectralShellNorm_green_scaled (kr kt A B c N HR Hr Ht : ℝ)
    (hkr : 0 ≤ kr) (hkt : 0 < kt) (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hc : 0 < c) (hN : 0 < N) (D U : ℂ × ℂ) (W : ℂ)
    (hD : spectralShellNorm kr D ≤ A*Real.exp (HR-Hr))
    (hU : spectralShellNorm kt U ≤ B*N*Real.exp Ht)
    (hW : c*N*Real.exp HR ≤ ‖W‖) :
    spectralShellNorm kr ((U.1/W) • D) ≤ A*B/(c*kt)*Real.exp (Ht-Hr) := by
  have hw : 0 < ‖W‖ := lt_of_lt_of_le (by positivity : 0 < c*N*Real.exp HR) hW
  have hD0 := spectralShellNorm_nonneg kr hkr D
  have hU0 := spectralShellNorm_nonneg kt hkt.le U
  have hv := spectralShellNorm_value kt hkt U
  rw [spectralShellNorm_smul,norm_div]
  calc
    _ ≤ (spectralShellNorm kt U/kt)/‖W‖*spectralShellNorm kr D := by gcongr
    _ ≤ (B*N*Real.exp Ht/kt)/(c*N*Real.exp HR)*(A*Real.exp (HR-Hr)) := by gcongr
    _ = _ := by
      rw [Real.exp_sub,Real.exp_sub]
      field_simp

theorem spectralScalarGreenState_scaled_bound
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (k H : ℝ → ℝ)
    (A B c N HR r t : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 < c) (hN : 0 < N)
    (hkr : 0 < k r) (hkt : 0 < k t)
    (hD : ∀ s ∈ ({r,t} : Set ℝ), spectralShellNorm (k s) (D s) ≤ A*Real.exp (HR-H s))
    (hU : ∀ s ∈ ({r,t} : Set ℝ), spectralShellNorm (k s) (U s) ≤ B*N*Real.exp (H s))
    (hW : c*N*Real.exp HR ≤ ‖W‖)
    (hH : AntitoneOn H (Set.Icc (min r t) (max r t))) :
    spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ A*B/(c*k t) := by
  have hrr : r ∈ ({r,t} : Set ℝ) := by simp only [Set.mem_insert_iff,true_or]
  have htt : t ∈ ({r,t} : Set ℝ) := by simp only [Set.mem_insert_iff,Set.mem_singleton_iff,or_true]
  have hrmem : r ∈ Set.Icc (min r t) (max r t) := ⟨min_le_left _ _,le_max_left _ _⟩
  have htmem : t ∈ Set.Icc (min r t) (max r t) := ⟨min_le_right _ _,le_max_right _ _⟩
  have hconst : 0 ≤ A*B/(c*k t) := by positivity
  by_cases hrt : r ≤ t
  · rw [spectralScalarGreenState,ite_eq_left hrt]
    apply (spectralShellNorm_green_scaled (k r) (k t) A B c N HR (H r) (H t)
      hkr.le hkt hA hB hc hN (D r) (U t) W (hD r hrr) (hU t htt) hW).trans
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hH hrmem htmem hrt))) hconst
  · rw [spectralScalarGreenState,ite_eq_right hrt]
    have hw : 0 < ‖W‖ := lt_of_lt_of_le (by positivity : 0 < c*N*Real.exp HR) hW
    rw [spectralShellNorm_smul,norm_div]
    have hvalue := spectralShellNorm_value (k t) hkt (D t)
    have hvalue' := hvalue.trans (div_le_div_of_nonneg_right (hD t htt) hkt.le)
    have hUnonneg := spectralShellNorm_nonneg (k r) hkr.le (U r)
    calc
      _ ≤ (A*Real.exp (HR-H t)/(k t))/(c*N*Real.exp HR)*(B*N*Real.exp (H r)) := by
        gcongr
        exact hU r hrr
      _ = A*B/(c*k t)*Real.exp (H r-H t) := by
        rw [Real.exp_sub,Real.exp_sub]
        field_simp
      _ ≤ A*B/(c*k t) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hH htmem hrmem (le_of_not_ge hrt)))) hconst

end DefocusingNLS

end OAI
