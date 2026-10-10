import OAI.Analysis.LipschitzHilbert.Fourier.ScalarBandKernel

namespace OAI

/-! The basic and reverse-disparity estimates for the actual scalar time
operator with the original vertical cutoff and unprojected test. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped ENNReal FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem actual_scalar_band_basic (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := scalar_band_basic hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [←scalarBandForm_eq_kernel psi beta N topLength W center htop u hum f g]
  exact hmain N topLength W w center htop hW hw hwW hlo hhi u hum hu f g
    f.continuous.measurable g.continuous.measurable hfb hgb E F hE hF hEfin hFfin hgs hfs

theorem actual_scalar_band_reverse (hVariation : LepingleInput)
    (psi beta : SchwartzMap ℝ ℂ) (B c C a M : ℝ)
    (hB : 0<B) (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hbeta : ∀ y, beta y≠0 → |y|≤B/2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (topLength W w center : ℝ),
      0<topLength → 0<W → 0<w → w≤W → c+B*(w/W)≤w*center → w*center+B*(w/W)≤C →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N topLength) u
        (schwartzVerticalProjection beta W center f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := scalar_band_reverse hVariation psi beta B c C a M hB hc hC ha hM hpsi hbeta
  refine ⟨K,hK,?_⟩
  intro N topLength W w center htop hW hw hwW hlo hhi u hum hu f g hfb hgb
    E F hE hF hEfin hFfin hgs hfs
  rw [←scalarBandForm_eq_kernel psi beta N topLength W center htop u hum f g]
  exact hmain N topLength W w center htop hW hw hwW hlo hhi u hum hu f g
    f.continuous.measurable g.continuous.measurable hfb hgb E F hE hF hEfin hFfin hgs hfs

end LipschitzHilbert.PacketRepresentation

end

end OAI
