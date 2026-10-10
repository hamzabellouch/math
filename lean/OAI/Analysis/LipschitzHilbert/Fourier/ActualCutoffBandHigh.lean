import OAI.Analysis.LipschitzHilbert.Fourier.ActualBandHigh
import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedBandProjection

namespace OAI

/-! The actual high-disparity estimate with the original band cutoff on
the input. The original bounded input need not itself have a spectrum. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem slopeKernelOperator_schwartz_smul (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (c : ℂ) (z : ℝ×ℝ) :
    slopeKernelOperator K u (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=c*slopeKernelOperator K u f z := by
  unfold slopeKernelOperator
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [smul_apply,smul_eq_mul]
  ring

theorem bandProjection_pairing_normalize (p : SchwartzMap ℝ ℂ) (w : ℝ)
    (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖∫ z, slopeKernelOperator K u (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖=
      verticalProjectionCost p*
        ‖∫ z, slopeKernelOperator K u (normalizedBandProjection p w f) z*star (g z) ∂planeMeasure‖ := by
  have hC := verticalProjectionCost_pos p
  have hp : schwartzVerticalProjection p w 0 f=
      (verticalProjectionCost p : ℂ) • normalizedBandProjection p w f := by
    unfold normalizedBandProjection
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast hC.ne' : (verticalProjectionCost p : ℂ)≠0),one_smul]
  rw [hp]
  simp_rw [slopeKernelOperator_schwartz_smul,mul_assoc]
  rw [integral_const_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hC.le]

theorem actual_cutoff_band_high (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (psi p : SchwartzMap ℝ ℂ) (c C a M : ℝ)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s : ℝ, p s≠0 → c≤s ∧ s≤C) :
    ∃ D A L0 : ℝ, 0<D ∧ 0<A ∧ 16≤L0 ∧ ∀ L : ℝ, L0≤L →
    ∀ (N : ℕ) (topLength W w : ℝ), 0<topLength → 0<W → 0<w → w≤W →
      5*(w/W)≤c/2 → c/2≤C → topLength≤Real.exp (-(L^(97/100:ℝ))) →
      (∀ j : Fin N, D*w≤topLength/(2:ℝ)^j.val) →
    ∀ (field : Plane → ℝ), LipschitzWith 1 field → (∀ z, |field z|≤1/4) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ),
    ∀ (F E ratio : ℝ), 0<F → 0<E → 0<ratio → E=ratio^2*F → Real.log ratio=L →
      (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      (∫ z, ‖f z‖ ∂planeMeasure)≤F → (∫ z, ‖g z‖ ∂planeMeasure)≤E →
      (∫ z, ‖f z‖^2 ∂planeMeasure)≤F → (∫ z, ‖g z‖^2 ∂planeMeasure)≤E →
    ∀ l r m : ℝ, 600*(r-l)≤1 →
      (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      Real.exp (L^(9/10:ℝ))≤m → m≤2*Real.exp (L^(9/10:ℝ)) → W=m*w →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength)
        (fun z => field (planeCoordinates z)) (schwartzVerticalProjection p w 0 f) z*
          star (g z) ∂planeMeasure‖≤A*L^(-19:ℝ)*Real.sqrt F*Real.sqrt E := by
  obtain ⟨D,A,L0,hD,hA,hL0,hmain⟩ := actual_band_high hVariation hLL psi c C a M hc hC ha hM hpsi
  refine ⟨D,verticalProjectionCost p*A,L0,hD,mul_pos (verticalProjectionCost_pos p) hA,hL0,?_⟩
  intro L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength field hfield hfieldBound
    f g F E ratio hF hE hr heq hlog hfInf hgInf hfL1 hgL1 hfE hgE l r m hstrip hfstrip hgstrip
    hmlo hmhi hWeq
  have hsizes := normalizedBandProjection_sizes p w hw f
  have h := hmain L hL N topLength W w htop hW hw hwW hsmall hcC htime hlength
    field hfield hfieldBound (normalizedBandProjection p w f) g
    (normalizedBandProjection_band p w c C hp f) F E ratio hF hE hr heq hlog
    (normalizedBandProjection_uniform p w hw f hfInf) hgInf (hsizes.1.trans hfL1) hgL1
    (hsizes.2.trans hfE) hgE l r m hstrip
    (normalizedBandProjection_support p w hw f (Icc l r) hfstrip) hgstrip hmlo hmhi hWeq
  rw [bandProjection_pairing_normalize]
  exact (mul_le_mul_of_nonneg_left h (verticalProjectionCost_pos p).le).trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
