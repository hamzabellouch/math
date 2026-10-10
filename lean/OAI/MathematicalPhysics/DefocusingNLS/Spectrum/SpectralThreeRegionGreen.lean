import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralThreeRegionTransfer
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDirichletGreenScaled
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOutgoingExtensionBound

namespace OAI

/-! Extend the Dirichlet/outgoing construction across a turning interval and
the oscillatory region. No exponential comparison between channels is needed. -/

open Set
namespace DefocusingNLS

theorem spectralScalar_three_region_green_and_extension (R a b E A C D c : ℝ)
    (hRa : R ≤ a) (hab : a ≤ b) (hbE : b ≤ E)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 1 ≤ D) (hc : 0 < c)
    (V : ℝ → ℂ) (k H : ℝ → ℝ)
    (hV : ContinuousOn V (Icc R E)) (hk : ∀ r ∈ Icc R E, 0 < k r)
    (hH : AntitoneOn H (Icc R a)) (ha : H a = 0)
    (U : ℝ → ℂ × ℂ) (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ r ∈ Ioo R E, HasDerivAt U (spectralScalarField (V r) (U r)) r)
    (hN : 0 < spectralShellNorm (k a) (U a))
    (hvalue : c*Real.exp (H R)*spectralShellNorm (k a) (U a) ≤ k R*‖(U R).1‖)
    (hleft : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc R a,
        spectralShellNorm (k r) (q r) ≤ A*Real.exp (H R-H r)*spectralShellNorm (k R) (q R) ∧
        spectralShellNorm (k r) (q r) ≤ A*Real.exp (H r)*spectralShellNorm (k a) (q a))
    (hcentral : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc a b, spectralShellNorm (k r) (q r) ≤ C*spectralShellNorm (k a) (q a))
    (hright : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc b E, spectralShellNorm (k r) (q r) ≤ D*spectralShellNorm (k b) (q b)) :
    ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
      (∀ r ∈ Icc R E, HasDerivAt Y (spectralScalarField (V r) (Y r)) r) ∧
      W ≠ 0 ∧ (∀ r ∈ Icc R E, spectralScalarWronskian (Y r) (U r) = W) ∧
      (∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState Y U W r t) ≤
          max A (C*A*D)*max A (C*D)/(c*k t)) ∧
      ∀ z : ℂ, ∀ r ∈ Icc R E,
        spectralShellNorm (k r) ((z/(U R).1) • U r) ≤ (max A (C*D)/c)*k R*‖z‖ := by
  let N := spectralShellNorm (k a) (U a)
  let G := spectralTruncatedAction a H
  have hRE : R ≤ E := hRa.trans (hab.trans hbE)
  have hGR : G R = H R := by simp only [G,spectralTruncatedAction,ite_eq_left hRa]
  have hUb : ∀ r ∈ Icc R E, spectralShellNorm (k r) (U r) ≤ max A (C*D)*N*Real.exp (G r) := by
    intro r hr
    have hh := spectralThreeRegion_bound R a b E A C D N hRa hab hbE hA hC hD hN.le
      (fun t => spectralShellNorm (k t) (U t)) H ha
      (fun t ht => (hleft U hUc hUD t ht).2) (hcentral U hUc hUD) (hright U hUc hUD) r hr
    convert hh using 1
    ring
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hYb,hWb,hgreen⟩ :=
    spectralScalar_dirichlet_green_scaled_data R E (max A (C*A*D)) (max A (C*D)) c N
      hRE (hA.trans (le_max_left _ _)) (hA.trans (le_max_left _ _)) hc hN V k G hV hk
      (spectralTruncatedAction_antitone R a E hRa (hab.trans hbE) H hH ha) U hUc hUD hUb
      (by rw [hGR]; simpa only [N,mul_assoc,mul_left_comm,mul_comm] using hvalue)
      (by
        intro q hq hqD r hr
        rw [hGR]
        exact spectralThreeRegion_forward R a b E A C D hRa hab hbE hA hC hD
          (fun t => spectralShellNorm (k t) (q t)) H
          (spectralShellNorm_nonneg _ (hk R ⟨le_rfl,hRE⟩).le _) ha
          (fun t ht => (hleft q hq hqD t ht).1) (hcentral q hq hqD) (hright q hq hqD) r hr)
  refine ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,?_⟩
  intro z r hr
  apply spectralOutgoing_extension_bound (k r) (k R) (max A (C*D)) c N (G r) (G R)
    (U r) (U R) z (hA.trans (le_max_left _ _)) hc hN
  · exact spectralTruncatedAction_antitone R a E hRa (hab.trans hbE) H hH ha
      ⟨le_rfl,hRE⟩ hr hr.1
  · exact hUb r hr
  · rw [hGR]
    simpa only [N,mul_assoc,mul_left_comm,mul_comm] using hvalue

theorem spectralScalar_three_region_green (R a b E A C D c : ℝ)
    (hRa : R ≤ a) (hab : a ≤ b) (hbE : b ≤ E)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 1 ≤ D) (hc : 0 < c)
    (V : ℝ → ℂ) (k H : ℝ → ℝ)
    (hV : ContinuousOn V (Icc R E)) (hk : ∀ r ∈ Icc R E, 0 < k r)
    (hH : AntitoneOn H (Icc R a)) (ha : H a = 0)
    (U : ℝ → ℂ × ℂ) (hUc : ContinuousOn U (Icc R E))
    (hUD : ∀ r ∈ Ioo R E, HasDerivAt U (spectralScalarField (V r) (U r)) r)
    (hN : 0 < spectralShellNorm (k a) (U a))
    (hvalue : c*Real.exp (H R)*spectralShellNorm (k a) (U a) ≤ k R*‖(U R).1‖)
    (hleft : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc R a,
        spectralShellNorm (k r) (q r) ≤ A*Real.exp (H R-H r)*spectralShellNorm (k R) (q R) ∧
        spectralShellNorm (k r) (q r) ≤ A*Real.exp (H r)*spectralShellNorm (k a) (q a))
    (hcentral : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc a b, spectralShellNorm (k r) (q r) ≤ C*spectralShellNorm (k a) (q a))
    (hright : ∀ q : ℝ → ℂ × ℂ, ContinuousOn q (Icc R E) →
      (∀ r ∈ Ioo R E, HasDerivAt q (spectralScalarField (V r) (q r)) r) →
      ∀ r ∈ Icc b E, spectralShellNorm (k r) (q r) ≤ D*spectralShellNorm (k b) (q b)) :
    ∃ (Y : ℝ → ℂ × ℂ) (W : ℂ), Continuous Y ∧ Y R = (0,(k R : ℂ)) ∧
      (∀ r ∈ Icc R E, HasDerivAt Y (spectralScalarField (V r) (Y r)) r) ∧
      W ≠ 0 ∧ (∀ r ∈ Icc R E, spectralScalarWronskian (Y r) (U r) = W) ∧
      ∀ r ∈ Icc R E, ∀ t ∈ Icc R E,
        spectralShellNorm (k r) (spectralScalarGreenState Y U W r t) ≤
          max A (C*A*D)*max A (C*D)/(c*k t) := by
  obtain ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen,_⟩ :=
    spectralScalar_three_region_green_and_extension R a b E A C D c hRa hab hbE
      hA hC hD hc V k H hV hk hH ha U hUc hUD hN hvalue hleft hcentral hright
  exact ⟨Y,W,hYc,hYR,hYD,hW,hdet,hgreen⟩

end DefocusingNLS

end OAI
