import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarReverseTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellGreenBounds

namespace OAI

/-! Construct the Dirichlet comparison and its nonzero Wronskian from the
scalar transfer estimate and the outgoing value bound. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_dirichlet_green_data (R E C c : ℝ) (hRE : R ≤ E)
    (hC : 0 ≤ C) (hc : 0 < c) (V : ℝ → ℂ) (k H : ℝ → ℝ)
    (hV : ContinuousOn V (Icc R E)) (hk : ∀ r ∈ Icc R E, 0 < k r)
    (hH : AntitoneOn H (Icc R E)) (U : ℝ → ℂ × ℂ)
    (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ r ∈ Ioo R E, HasDerivAt U (spectralScalarField (V r) (U r)) r)
    (hUb : ∀ r ∈ Icc R E, spectralShellNorm (k r) (U r) ≤ C*Real.exp (H r))
    (hUR : c*Real.exp (H R) ≤ k R*‖(U R).1‖)
    (htransfer : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc R E, spectralShellNorm (k r) (q r) ≤
        C*Real.exp (H R-H r)*spectralShellNorm (k R) (q R)) :
    ∃ (D : ℝ → ℂ × ℂ) (W : ℂ),
      Continuous D ∧ D R = (0,(k R : ℂ)) ∧
      (∀ r ∈ Icc R E, HasDerivAt D (spectralScalarField (V r) (D r)) r) ∧
      W ≠ 0 ∧
      (∀ r ∈ Icc R E, spectralScalarWronskian (D r) (U r) = W) ∧
      (∀ r ∈ Icc R E, spectralShellNorm (k r) (D r) ≤ C*Real.exp (H R-H r)) ∧
      c*Real.exp (H R) ≤ ‖W‖ ∧
      ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState D U W r t) ≤ C^2/(c*k t) := by
  obtain ⟨D,hDc,hDR,hDD⟩ := spectralScalar_local_exists R E hRE V hV (0,(k R : ℂ))
  have hkR := hk R ⟨le_rfl,hRE⟩
  let W := spectralScalarWronskian (D R) (U R)
  have hWnorm : ‖W‖ = k R*‖(U R).1‖ := by
    simp only [W,hDR,spectralScalarWronskian,zero_mul,zero_sub,norm_neg,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hkR]
  have hW : c*Real.exp (H R) ≤ ‖W‖ := hWnorm ▸ hUR
  have hW0 : W ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (mul_pos hc (Real.exp_pos _)) hW)
  have hDN : spectralShellNorm (k R) (D R) = 1 := by
    rw [hDR]
    simp only [spectralShellNorm,norm_zero,mul_zero,zero_add,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hkR,inv_mul_cancel₀ hkR.ne']
  have hDb (r : ℝ) (hr : r ∈ Icc R E) :
      spectralShellNorm (k r) (D r) ≤ C*Real.exp (H R-H r) := by
    simpa only [hDN,mul_one] using htransfer D hDc.continuousOn
      (fun t ht => hDD t ⟨ht.1.le,ht.2.le⟩) r hr
  have hdet (r : ℝ) (hr : r ∈ Icc R E) : spectralScalarWronskian (D r) (U r) = W := by
    have hsub : Icc R r ⊆ Icc R E := Icc_subset_Icc le_rfl hr.2
    exact spectralScalarWronskian_eq R r hr.1 V D U (hDc.continuousOn.mono hsub)
      (hUc.mono hsub) (fun t ht => hDD t ⟨ht.1.le,ht.2.le.trans hr.2⟩)
      (fun t ht => hUD t ⟨ht.1,ht.2.trans_le hr.2⟩)
  refine ⟨D,W,hDc,hDR,hDD,hW0,hdet,hDb,hW,?_⟩
  intro r hr t ht
  apply spectralScalarGreenState_shell_bound D U W k H C c (H R) r t hC hc (hk r hr) (hk t ht)
  · intro s hs
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hs : s = r ∨ s = t) with rfl | rfl
    · exact hDb _ hr
    · exact hDb _ ht
  · intro s hs
    rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hs : s = r ∨ s = t) with rfl | rfl
    · exact hUb _ hr
    · exact hUb _ ht
  · exact hW
  · exact hH.mono (fun s hs => ⟨(le_min hr.1 ht.1).trans hs.1,
      hs.2.trans (max_le hr.2 ht.2)⟩)

end DefocusingNLS

end OAI
