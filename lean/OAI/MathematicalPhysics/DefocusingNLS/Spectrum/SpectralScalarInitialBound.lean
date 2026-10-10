import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarTransferKernel

namespace OAI

/-! The homogeneous term in variation of constants is controlled in the same
weighted norm as the forcing kernel. -/

namespace DefocusingNLS

theorem spectralScalarWronskian_shell_bound (k : ℝ) (hk : 0<k) (u v : ℂ × ℂ) :
    ‖spectralScalarWronskian u v‖≤ spectralShellNorm k u*spectralShellNorm k v := by
  have he : spectralShellNorm k u*spectralShellNorm k v=
      k^2*‖u.1‖*‖v.1‖+‖u.1‖*‖v.2‖+‖u.2‖*‖v.1‖+
        k⁻¹^2*‖u.2‖*‖v.2‖ := by
    dsimp only [spectralShellNorm]
    field_simp
    ring
  have hb : ‖spectralScalarWronskian u v‖≤‖u.1‖*‖v.2‖+‖u.2‖*‖v.1‖ := by
    simpa only [spectralScalarWronskian,norm_mul] using norm_sub_le (u.1*v.2) (u.2*v.1)
  rw [he]
  have h₁ : 0≤k^2*‖u.1‖*‖v.1‖ := by positivity
  have h₂ : 0≤k⁻¹^2*‖u.2‖*‖v.2‖ := by positivity
  linarith

theorem spectralScalarInitialTerm_bound
    (D U : ℝ → ℂ × ℂ) (W : ℂ) (q : ℂ × ℂ)
    (kr kt C c Hr Ht r t : ℝ)
    (hkr : 0≤ kr) (hkt : 0<kt) (hC : 0≤ C) (hc : 0<c) (hW : c≤‖W‖)
    (hDr : spectralShellNorm kr (D r)≤ C*Real.exp Hr)
    (hDt : spectralShellNorm kt (D t)≤ C*Real.exp Ht)
    (hUr : spectralShellNorm kr (U r)≤ C*Real.exp (-Hr))
    (hUt : spectralShellNorm kt (U t)≤ C*Real.exp (-Ht)) :
    spectralShellNorm kr ((spectralScalarWronskian q (U t)/W) • D r+
      (spectralScalarWronskian (D t) q/W) • U r)≤
      (2*C^2/c)*Real.exp |Hr-Ht| * spectralShellNorm kt q := by
  have hW0 : 0<‖W‖ := hc.trans_le hW
  have hn := spectralShellNorm_nonneg kt hkt.le q
  have hd0 := spectralShellNorm_nonneg kr hkr (D r)
  have hu0 := spectralShellNorm_nonneg kr hkr (U r)
  have hU0 := spectralShellNorm_nonneg kt hkt.le (U t)
  have hD0 := spectralShellNorm_nonneg kt hkt.le (D t)
  have hexp1 : Hr-Ht≤|Hr-Ht| := le_abs_self _
  have hexp2 : Ht-Hr≤|Hr-Ht| := by simpa only [abs_sub_comm] using le_abs_self (Ht-Hr)
  have hfirst : (spectralShellNorm kt q*spectralShellNorm kt (U t))/‖W‖*
      spectralShellNorm kr (D r)≤ C^2/c*Real.exp (Hr-Ht)*spectralShellNorm kt q := by
    calc
      _ ≤ (spectralShellNorm kt q*(C*Real.exp (-Ht)))/c*(C*Real.exp Hr) := by gcongr
      _ = _ := by rw [Real.exp_sub,Real.exp_neg]; field_simp
  have hsecond : (spectralShellNorm kt (D t)*spectralShellNorm kt q)/‖W‖*
      spectralShellNorm kr (U r)≤ C^2/c*Real.exp (Ht-Hr)*spectralShellNorm kt q := by
    calc
      _ ≤ ((C*Real.exp Ht)*spectralShellNorm kt q)/c*(C*Real.exp (-Hr)) := by gcongr
      _ = _ := by rw [Real.exp_sub,Real.exp_neg]; field_simp
  calc
    _ ≤ spectralShellNorm kr ((spectralScalarWronskian q (U t)/W) • D r)+
        spectralShellNorm kr ((spectralScalarWronskian (D t) q/W) • U r) :=
      spectralShellNorm_add_le kr hkr _ _
    _ = ‖spectralScalarWronskian q (U t)‖/‖W‖*spectralShellNorm kr (D r)+
        ‖spectralScalarWronskian (D t) q‖/‖W‖*spectralShellNorm kr (U r) := by
      rw [spectralShellNorm_smul,spectralShellNorm_smul,norm_div,norm_div]
    _ ≤ (spectralShellNorm kt q*spectralShellNorm kt (U t))/‖W‖*spectralShellNorm kr (D r)+
        (spectralShellNorm kt (D t)*spectralShellNorm kt q)/‖W‖*spectralShellNorm kr (U r) := by
      gcongr
      · exact spectralScalarWronskian_shell_bound kt hkt _ _
      · exact spectralScalarWronskian_shell_bound kt hkt _ _
    _ ≤ C^2/c*Real.exp (Hr-Ht)*spectralShellNorm kt q+
        C^2/c*Real.exp (Ht-Hr)*spectralShellNorm kt q := add_le_add hfirst hsecond
    _ ≤ C^2/c*Real.exp |Hr-Ht| * spectralShellNorm kt q+
        C^2/c*Real.exp |Hr-Ht| * spectralShellNorm kt q := by gcongr
    _ = _ := by ring

end DefocusingNLS

end OAI
