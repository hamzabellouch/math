import OAI.Analysis.LipschitzHilbert.Estimates.HilbertTimeDecomposition

namespace OAI

/-! The complementary endpoint cases: no very-short segment when the
inner endpoint is already large, and no packet segment for wide bands. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem hilbertMiddleLong_bound :
    ∃ B : ℝ, 0≤B ∧ ∀ epsilon T R : ℝ, 0<epsilon → epsilon≤T → T≤R →
      ∃ N : ℕ, epsilon≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*epsilon ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (p : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection p w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection p w 0 f) g‖≤
        (verticalProjectionCost p*(B+2*Real.log (R/T)))*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hmid⟩ := hilbertProjected_middle_error
  refine ⟨B,hB,?_⟩
  intro epsilon T R he heT hTR
  obtain ⟨N,hlo,hhi,hbound⟩ := hmid epsilon T he heT
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hm := hbound u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hl := sharpHilbertProjection_long_pairing T R (he.trans_le heT) hTR u hu p w hw
    f g hf hg l r hwidth hfstrip hgstrip
  rw [kernelPairing_sharp_split epsilon T R he heT hTR u hu.continuous.measurable]
  rw [show ∀ a b c : ℂ, a+b-c=(a-c)+b by intros; ring]
  exact (norm_add_le _ _).trans ((add_le_add hm hl).trans_eq (by ring))

theorem hilbertShortLong_bound (hH : HorizontalHilbertInput) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon T R : ℝ, 0<epsilon → epsilon≤T → T≤R → T≤1/4 →
      ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
      ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) → (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection cutoff w 0 f) g‖≤
        (verticalProjectionCost cutoff*(2*Real.log (R/T))+
          2*T*verticalProjectionCost (verticalDerivativeProfile cutoff)/w)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨C,hC,hhor⟩ := horizontalHilbertProjection_restricted_pairing hH
  refine ⟨C,hC,?_⟩
  intro epsilon T R he heT hTR hTquarter p q hp hpq u hu hub cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hs := hilbertProjected_short_error epsilon T he heT hTquarter u hu hub cutoff w hw f g hf hg
  have hh := hhor p q hp hpq epsilon T he heT cutoff w hw f g hf hg
  have hl := sharpHilbertProjection_long_pairing T R (he.trans_le heT) hTR u hu cutoff w hw
    f g hf hg l r hwidth hfstrip hgstrip
  have hs' := (norm_le_insert'
    (kernelPairing (sharpTimeKernel epsilon T) u (schwartzVerticalProjection cutoff w 0 f) g)
    (kernelPairing (sharpTimeKernel epsilon T) (fun _ => 0) (schwartzVerticalProjection cutoff w 0 f) g)).trans
    (add_le_add hh hs)
  rw [kernelPairing_sharp_split epsilon T R he heT hTR u hu.continuous.measurable]
  exact (norm_add_le _ _).trans ((add_le_add hs' hl).trans_eq (by ring))

end LipschitzHilbert.PacketRepresentation

end

end OAI
