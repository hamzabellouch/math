import OAI.Analysis.LipschitzHilbert.Estimates.SharpTimeSplit
import OAI.Analysis.LipschitzHilbert.Estimates.HilbertArbitraryEndpoint
import OAI.Analysis.LipschitzHilbert.Estimates.VeryShortHilbertError
import OAI.Analysis.LipschitzHilbert.Estimates.LongHilbertPairing
import OAI.Analysis.LipschitzHilbert.Estimates.HorizontalHilbertPairing

namespace OAI

/-! Assembly of the actual short, middle and long time pieces. The
middle term is the finite annular operator already estimated by the
packet argument; all other terms have explicit restricted bounds. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem kernelPairing_projection_normalize (K : ℝ → ℂ) (u : (ℝ×ℝ) → ℝ)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (f g : SchwartzMap (ℝ×ℝ) ℂ) :
    kernelPairing K u (schwartzVerticalProjection p w 0 f) g=
      (verticalProjectionCost p : ℂ)*kernelPairing K u (normalizedBandProjection p w f) g := by
  have heq : schwartzVerticalProjection p w 0 f=
      (verticalProjectionCost p : ℂ) • normalizedBandProjection p w f := by
    unfold normalizedBandProjection
    rw [smul_smul,mul_inv_cancel₀ (by exact_mod_cast (verticalProjectionCost_pos p).ne' :
      (verticalProjectionCost p : ℂ)≠0),one_smul]
  rw [heq,kernelPairing_smul]

theorem hilbertProjected_middle_error :
    ∃ B : ℝ, 0≤B ∧ ∀ s T : ℝ, 0<s → s≤T →
      ∃ N : ℕ, s≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*s ∧
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u →
      ∀ (p : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) →
        (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel s T) u (schwartzVerticalProjection p w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection p w 0 f) g‖≤
        (verticalProjectionCost p*B)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  obtain ⟨B,hB,hmain⟩ := hilbertArbitraryEndpoint_pairing
  refine ⟨B,hB,?_⟩
  intro s T hs hsT
  obtain ⟨N,hlo,hhi,hbound⟩ := hmain s T hs hsT
  refine ⟨N,hlo,hhi,?_⟩
  intro u hu p w hw f g hf hg l r hwidth hfstrip hgstrip
  have hb := hbound u hu (normalizedBandProjection p w f) g
    (normalizedBandProjection_uniform p w hw f hf) hg l r hwidth
    (normalizedBandProjection_support p w hw f _ hfstrip) hgstrip
  have hsize := (normalizedBandProjection_sizes p w hw f).1
  rw [kernelPairing_projection_normalize,kernelPairing_projection_normalize,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg (verticalProjectionCost_pos _).le]
  calc
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖normalizedBandProjection p w f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) :=
      mul_le_mul_of_nonneg_left hb (verticalProjectionCost_pos _).le
    _ ≤ verticalProjectionCost p*(B*min
        (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)) := by
      apply mul_le_mul_of_nonneg_left _ (verticalProjectionCost_pos _).le
      exact mul_le_mul_of_nonneg_left
        (min_le_min (mul_le_mul_of_nonneg_left hsize (by norm_num)) le_rfl) hB
    _ = _ := by ring

theorem hilbertProjected_short_error (epsilon s : ℝ) (he : 0<epsilon) (hes : epsilon≤s)
    (hs : s≤1/4) (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u) (hub : ∀ z, |u z|≤1)
    (p : SchwartzMap ℝ ℂ) (w : ℝ) (hw : 0<w)
    (f g : SchwartzMap (ℝ×ℝ) ℂ) (hf : ∀ z, ‖f z‖≤1) (hg : ∀ z, ‖g z‖≤1) :
    ‖kernelPairing (sharpTimeKernel epsilon s) u (schwartzVerticalProjection p w 0 f) g-
      kernelPairing (sharpTimeKernel epsilon s) (fun _ => 0) (schwartzVerticalProjection p w 0 f) g‖≤
      (2*s*verticalProjectionCost (verticalDerivativeProfile p)/w)*
        min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure) := by
  have hsp : 0<s := he.trans_le hes
  have hK := sharpTimeKernel_integrable epsilon s he hsp
  have hKm := sharpTimeKernel_measurable epsilon s
  unfold kernelPairing
  rw [←integral_sub (kernelPairing_integrable _ hKm hK u hu.continuous.measurable _ g)
    (kernelPairing_integrable _ hKm hK (fun _ => 0) measurable_const _ g)]
  simp_rw [←sub_mul]
  exact veryShortHilbertProjection_pairing epsilon s he hsp hs u hu hub p w hw f g hf hg

theorem hilbertTimeDecomposition_bound (hH : HorizontalHilbertInput) :
    ∃ B C : ℝ, 0≤B ∧ 0<C ∧ ∀ epsilon s T R : ℝ,
      0<epsilon → epsilon≤s → s≤T → T≤R → s≤1/4 →
      ∃ N : ℕ, s≤T/(2:ℝ)^N ∧ T/(2:ℝ)^N<2*s ∧
      ∀ p q : ℝ, (p=3/2 ∨ p=4) → p.HolderConjugate q →
      ∀ (u : (ℝ×ℝ) → ℝ), LipschitzWith 2 u → (∀ z, |u z|≤1) →
      ∀ (cutoff : SchwartzMap ℝ ℂ) (w : ℝ), 0<w →
      ∀ (f g : SchwartzMap (ℝ×ℝ) ℂ), (∀ z, ‖f z‖≤1) → (∀ z, ‖g z‖≤1) →
      ∀ l r : ℝ, r-l≤1/4 → (∀ z, z.1∉Icc l r → f z=0) →
        (∀ z, z.1∉Icc l r → g z=0) →
      ‖kernelPairing (sharpTimeKernel epsilon R) u (schwartzVerticalProjection cutoff w 0 f) g-
        kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u
          (schwartzVerticalProjection cutoff w 0 f) g‖≤
        (verticalProjectionCost cutoff*(B+2*Real.log (R/T))+
          2*s*verticalProjectionCost (verticalDerivativeProfile cutoff)/w)*
          min (4*∫ z, ‖f z‖ ∂planeMeasure) (∫ z, ‖g z‖ ∂planeMeasure)+
        (C*verticalProjectionCost cutoff)*(∫ z, ‖f z‖ ∂planeMeasure)^(1/p)*
          (∫ z, ‖g z‖ ∂planeMeasure)^(1/q) := by
  obtain ⟨B,hB,hmid⟩ := hilbertProjected_middle_error
  obtain ⟨C,hC,hhor⟩ := horizontalHilbertProjection_restricted_pairing hH
  refine ⟨B,C,hB,hC,?_⟩
  intro epsilon s T R he hes hsT hTR hsquarter
  have hs : 0<s := he.trans_le hes
  obtain ⟨N,hlo,hhi,hmidbound⟩ := hmid s T hs hsT
  refine ⟨N,hlo,hhi,?_⟩
  intro p q hp hpq u hu hub cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  let F := schwartzVerticalProjection cutoff w 0 f
  let A := kernelPairing (sharpTimeKernel epsilon s) u F g
  let H := kernelPairing (sharpTimeKernel epsilon s) (fun _ => 0) F g
  let M := kernelPairing (sharpTimeKernel s T) u F g
  let J := kernelPairing (finiteTimeKernel hilbertTimeKernel N (T/2)) u F g
  let V := kernelPairing (sharpTimeKernel T R) u F g
  have hshort := hilbertProjected_short_error epsilon s he hes hsquarter u hu hub
    cutoff w hw f g hf hg
  have hmiddle := hmidbound u hu cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hlong := sharpHilbertProjection_long_pairing T R (hs.trans_le hsT) hTR
    u hu cutoff w hw f g hf hg l r hwidth hfstrip hgstrip
  have hhorizontal := hhor p q hp hpq epsilon s he hes cutoff w hw f g hf hg
  have hsplit : kernelPairing (sharpTimeKernel epsilon R) u F g=A+(M+V) := by
    rw [kernelPairing_sharp_split epsilon s R he hes (hsT.trans hTR) u hu.continuous.measurable,
      kernelPairing_sharp_split s T R hs hsT hTR u hu.continuous.measurable]
  have heq : kernelPairing (sharpTimeKernel epsilon R) u F g-J=(A-H)+(M-J)+V+H := by
    rw [hsplit]
    ring
  change ‖kernelPairing (sharpTimeKernel epsilon R) u F g-J‖≤_
  rw [heq]
  calc
    _ ≤ ‖A-H‖+‖M-J‖+‖V‖+‖H‖ := by
      calc
        _ ≤ ‖A-H+(M-J)+V‖+‖H‖ := norm_add_le _ _
        _ ≤ (‖A-H+(M-J)‖+‖V‖)+‖H‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl
    _ ≤ _ := by
      have h := add_le_add (add_le_add (add_le_add hshort hmiddle) hlong) hhorizontal
      exact h.trans_eq (by ring)

end LipschitzHilbert.PacketRepresentation

end

end OAI
