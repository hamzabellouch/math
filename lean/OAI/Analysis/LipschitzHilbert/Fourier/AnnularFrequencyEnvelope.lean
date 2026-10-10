import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedFrequencySymbol
import OAI.Analysis.LipschitzHilbert.Fourier.L1FrequencyMultiplier

namespace OAI

/-! A bounded direction and compact annular and vertical windows give a
single integrable frequency envelope, uniformly in the spatial point. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation

theorem annularBandSymbol_support_bounds
    (psi beta : SchwartzMap ℝ ℂ) (l W center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) (z omega : ℝ×ℝ)
    (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    |omega.1|≤M/l+U*(|center|+B/W) ∧ |omega.2|≤|center|+B/W := by
  have hy := hbeta _ hb
  change |W*(omega.2-center)|≤B at hy
  rw [abs_mul,abs_of_pos hW] at hy
  have hy' : |omega.2-center|≤B/W := (le_div_iff₀ hW).mpr (by nlinarith)
  have hy'' : |omega.2|≤|center|+B/W := by
    calc
      |omega.2|=|(omega.2-center)+center| := by congr 1; ring
      _≤|omega.2-center|+|center| := abs_add_le _ _
      _≤|center|+B/W := by linarith
  have hx := hpsi _ hp
  rw [abs_mul,abs_of_pos hl] at hx
  have hx' : |omega.1+u z*omega.2|≤M/l := (le_div_iff₀ hl).mpr (by nlinarith)
  refine ⟨?_,hy''⟩
  calc
    |omega.1|=|(omega.1+u z*omega.2)-(u z*omega.2)| := by congr 1; ring
    _≤|omega.1+u z*omega.2|+|u z*omega.2| := abs_sub _ _
    _≤M/l+U*(|center|+B/W) := by
      rw [abs_mul]
      exact add_le_add hx' (mul_le_mul (hu z) hy'' (abs_nonneg _) hU)

theorem exists_frequency_rectangle_envelope
    (m : (ℝ×ℝ)×(ℝ×ℝ) → ℂ) (C R S : ℝ)
    (hbound : ∀ z omega, ‖m (z,omega)‖≤C)
    (hsupport : ∀ z omega, m (z,omega)≠0 → |omega.1|≤R ∧ |omega.2|≤S) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖m (z,omega)‖≤q omega := by
  let s : Set (ℝ×ℝ) := Icc (-R) R ×ˢ Icc (-S) S
  have hs : MeasurableSet s := measurableSet_Icc.prod measurableSet_Icc
  have hfin : planeMeasure s≠∞ := (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  refine ⟨s.indicator (fun _ => C), (integrableOn_const hfin).integrable_indicator hs,?_⟩
  intro z omega
  by_cases hm : m (z,omega)=0
  · have hC : 0≤C := (norm_nonneg (m (z,omega))).trans (hbound z omega)
    rw [hm,norm_zero]
    exact indicator_nonneg (fun _ _ => hC) _
  · have hmem : omega∈s := by
      obtain ⟨hR,hS⟩ := hsupport z omega hm
      exact ⟨abs_le.mp hR,abs_le.mp hS⟩
    rw [indicator_of_mem hmem]
    exact hbound z omega

theorem exists_partitionedFrequencySymbol_envelope
    (psi rho beta : SchwartzMap ℝ ℂ) (l W w theta center M B U : ℝ)
    (hl : 0<l) (hW : 0<W) (hU : 0≤U)
    (hpsi : ∀ s, psi s≠0 → |s|≤M) (hbeta : ∀ s, beta s≠0 → |s|≤B)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U) :
    ∃ q : ℝ×ℝ → ℝ, Integrable q planeMeasure ∧
      ∀ z omega, ‖partitionedFrequencySymbol psi rho beta l W w theta center u (z,omega)‖≤q omega := by
  apply exists_frequency_rectangle_envelope _
    (SchwartzMap.seminorm ℝ 0 0 psi*SchwartzMap.seminorm ℝ 0 0 rho*SchwartzMap.seminorm ℝ 0 0 beta)
    (M/l+U*(|center|+B/W)) (|center|+B/W)
    (partitionedFrequencySymbol_bound psi rho beta l W w theta center u)
  intro z omega hm
  have hp : psi (l*(omega.1+u z*omega.2))≠0 := by
    intro hp; exact hm (by simp [partitionedFrequencySymbol,hp])
  have hb : beta (symbolY W omega.2 center)≠0 := by
    intro hb; exact hm (by simp [partitionedFrequencySymbol,hb])
  exact annularBandSymbol_support_bounds psi beta l W center M B U hl hW hU hpsi hbeta u hu z omega hp hb

end LipschitzHilbert.PacketRepresentation

end

end OAI
