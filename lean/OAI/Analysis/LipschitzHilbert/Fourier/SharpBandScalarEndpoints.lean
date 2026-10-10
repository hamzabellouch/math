import OAI.Analysis.LipschitzHilbert.Fourier.CenteredBandProjection
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertTimeDecomposition
import OAI.Analysis.LipschitzHilbert.Fourier.RestrictedSchwartzSizes

namespace OAI

/-! The scalar basic and reverse-disparity estimates pass to every
actual sharp truncation, on the original restricted Schwartz inputs. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem actual_sharp_band_basic (hVariation : LepingleInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g‖≤
        C*Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E) := by
  obtain ⟨K,hK,hmain⟩ := actual_positive_band_basic hVariation hilbertAnnularSymbol p (1/2) 2
    (by norm_num) (by norm_num) hilbertAnnularSymbol_support hp
  obtain ⟨B,hB,herror⟩ := hilbertProjected_middle_error
  have hP := verticalProjectionCost_pos p
  refine ⟨K+4*(verticalProjectionCost p*B),by positivity,?_⟩
  intro epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hgs hfs l r hwidth hfstrip hgstrip
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,_,_,herr⟩ := herror epsilon R he heR
  have he1 := restrictedSchwartz_l1 g hg E hE hEfin hgs
  have hf1 := restrictedSchwartz_l1 f hf F hF hFfin hfs
  have hb := herr u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hmass : min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)≤
      4*(Real.sqrt (planeMeasure.real F)*Real.sqrt (planeMeasure.real E)) :=
    (min_le_min (mul_le_mul_of_nonneg_left hf1 (by norm_num)) he1).trans
      (min_mass_le_sqrt _ _ measureReal_nonneg measureReal_nonneg)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hP.le hB))
  have hm := hmain N (R/2) w (by positivity) hw u hu.continuous.measurable hub
    f g hf hg E F hE hF hEfin hFfin hgs hfs
  exact (norm_le_insert' _ _).trans ((add_le_add hm hb').trans_eq (by ring))

theorem actual_sharp_band_reverse (hVariation : LepingleInput) (p : SchwartzMap ℝ ℂ)
    (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, 0<epsilon → epsilon≤R → 0<w →
    ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
    ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
    ∀ E F : Set (ℝ×ℝ), MeasurableSet E → MeasurableSet F → planeMeasure E≠∞ → planeMeasure F≠∞ →
      0<planeMeasure.real F → 0<planeMeasure.real E → planeMeasure.real E≤planeMeasure.real F →
      (∀ z, z∉E → g z=0) → (∀ z, z∉F → f z=0) →
    ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g‖≤
        C*Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
          (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) := by
  obtain ⟨K,hK,hmain⟩ := actual_positive_band_reverse hVariation hilbertAnnularSymbol p (1/2) 2
    (by norm_num) (by norm_num) hilbertAnnularSymbol_support hp
  obtain ⟨B,hB,herror⟩ := hilbertProjected_middle_error
  have hP := verticalProjectionCost_pos p
  refine ⟨K+verticalProjectionCost p*B,by positivity,?_⟩
  intro epsilon R w he heR hw u hu hub f g hf hg E F hE hF hEfin hFfin hFpos hEpos hEF hgs hfs
    l r hwidth hfstrip hgstrip
  have hR : 0<R := he.trans_le heR
  obtain ⟨N,_,_,herr⟩ := herror epsilon R he heR
  have he1 := restrictedSchwartz_l1 g hg E hE hEfin hgs
  have hb := herr u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hmass : min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)≤
      Real.sqrt (planeMeasure.real F*planeMeasure.real E)*
        (planeMeasure.real E/planeMeasure.real F)^(9/20:ℝ) :=
    ((min_le_right _ _).trans he1).trans (reverse_mass_bound _ _ hFpos hEpos hEF)
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hmass (mul_nonneg hP.le hB))
  have hm := hmain N (R/2) w (by positivity) hw u hu.continuous.measurable hub
    f g hf hg E F hE hF hEfin hFfin hgs hfs
  exact (norm_le_insert' _ _).trans ((add_le_add hm hb').trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
