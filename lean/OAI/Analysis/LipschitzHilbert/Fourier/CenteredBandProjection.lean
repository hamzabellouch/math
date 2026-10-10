import OAI.Analysis.LipschitzHilbert.Fourier.ActualScalarBandBounds

namespace OAI

/-! The positive annular cutoff is exactly a centered cutoff at the same
width, so both scalar endpoint estimates apply to the original input. -/
noncomputable section
open Set MeasureTheory FourierTransform
open scoped FourierTransform ENNReal
namespace LipschitzHilbert.PacketRepresentation

def centeredPositiveCutoff (p : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  p.compSubConstCLM ℂ (-(3/2:ℝ))

theorem centeredPositiveCutoff_support (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∀ s, centeredPositiveCutoff p s≠0 → |s|≤1/2 := by
  intro s hs
  have h := hp (s+3/2) (by simpa only [centeredPositiveCutoff,
    SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add] using hs)
  exact abs_le.mpr ⟨by linarith [h.1],by linarith [h.2]⟩

theorem centeredPositiveCutoff_projection (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f : SchwartzMap (ℝ×ℝ) ℂ) :
    schwartzVerticalProjection (centeredPositiveCutoff p) w ((3/2)/w) f=
      schwartzVerticalProjection p w 0 f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier,centeredPositiveCutoff,
    SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,sub_zero]
  congr 2
  field_simp
  ring

theorem actual_positive_band_basic (hVariation : LepingleInput)
    (psi p : SchwartzMap ℝ ℂ) (a M : ℝ) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (top w : ℝ), 0<top → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N top) u
        (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hbound⟩ := actual_scalar_band_basic hVariation psi (centeredPositiveCutoff p)
    1 (1/2) (5/2) a M (by norm_num) (by norm_num) (by norm_num) ha hM hpsi
    (centeredPositiveCutoff_support p hp)
  refine ⟨K,hK,?_⟩
  intro N top w htop hw u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  have hcenter : w*((3/2)/w)=3/2 := mul_div_cancel₀ _ hw.ne'
  have h := hbound N top w w ((3/2)/w) htop hw hw le_rfl
    (by rw [div_self hw.ne',hcenter]; norm_num)
    (by rw [div_self hw.ne',hcenter]; norm_num)
    u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  rwa [centeredPositiveCutoff_projection p w hw] at h

theorem actual_positive_band_reverse (hVariation : LepingleInput)
    (psi p : SchwartzMap ℝ ℂ) (a M : ℝ) (ha : 0<a) (hM : 0<M)
    (hpsi : ∀ s, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ K : ℝ, 0<K ∧ ∀ (N : ℕ) (top w : ℝ), 0<top → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), Measurable u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
      ‖∫ z, slopeKernelOperator (finiteTimeKernel (𝓕⁻ psi : SchwartzMap ℝ ℂ) N top) u
        (schwartzVerticalProjection p w 0 f) z*star (g z) ∂planeMeasure‖≤
        K*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hbound⟩ := actual_scalar_band_reverse hVariation psi (centeredPositiveCutoff p)
    1 (1/2) (5/2) a M (by norm_num) (by norm_num) (by norm_num) ha hM hpsi
    (centeredPositiveCutoff_support p hp)
  refine ⟨K,hK,?_⟩
  intro N top w htop hw u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  have hcenter : w*((3/2)/w)=3/2 := mul_div_cancel₀ _ hw.ne'
  have h := hbound N top w w ((3/2)/w) htop hw hw le_rfl
    (by rw [div_self hw.ne',hcenter]; norm_num)
    (by rw [div_self hw.ne',hcenter]; norm_num)
    u hum hub f g hf hg E F hE hF hEfin hFfin hgs hfs
  rwa [centeredPositiveCutoff_projection p w hw] at h

end LipschitzHilbert.PacketRepresentation

end

end OAI
