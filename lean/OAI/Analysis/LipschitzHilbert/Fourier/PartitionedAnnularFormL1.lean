import OAI.Analysis.LipschitzHilbert.Fourier.NormalizedSymbolFormL1
import OAI.Analysis.LipschitzHilbert.Fourier.RescaledPartitionedSymbol
import OAI.Analysis.LipschitzHilbert.Estimates.ScaledWindowSpectrum

namespace OAI

/-! Exact finite representation including the manuscript slope partition
and the vertical bin window. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform BigOperators
namespace LipschitzHilbert.PacketRepresentation
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} [Fintype κ]

def partitionedAnnularSumL1 (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) : ℂ :=
  ∑ i : LatticeRow labels, ∑ k, ∫ z,
    (∫ omega, Real.fourierChar (z.1*omega.1+z.2*omega.2) •
      (psi (latticeLength topLength labels i*(omega.1+u z*omega.2))*
        rho (-symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2)/(w*omega.2))*
        beta (symbolY width omega.2 (center k))*
        (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
          latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
          planarFourier (f k) omega)) ∂planeMeasure)*star (g z k) ∂planeMeasure

theorem normalizedSymbolSum_eq_partitioned_annular_l1
    (psi rho beta : SchwartzMap ℝ ℂ) (chiA chiB : SchwartzMap (ℝ×ℝ) ℂ)
    (A B c C a M R H : ℝ) (hR : 0<R) (hH : 0<H)
    (hc : 0<c) (hC : 0<C) (ha : 0<a) (hM : 0<M)
    (hA : 0≤A) (hsmall : A≤a/4)
    (hpsi : ∀ s : ℝ, psi s≠0 → a≤|s| ∧ |s|≤M)
    (hsize : A+B+(M+A)/(H*c)≤R)
    (hchiA : ∀ z, chiA z≠0 → |z.1|≤A ∧ |z.2|≤B)
    (topLength width w : ℝ) (htop : 0<topLength) (hwidth : 0<width) (hw : 0<w)
    (labels : ∀ j, Finset (Label j)) (theta : ∀ j, labels j → ℝ) (center : κ → ℝ)
    (hparam : ∀ k, ‖(H*w*center k,H*w/width)‖≤R)
    (hlo : ∀ k, c+B*(w/width)≤w*center k)
    (hhi : ∀ k, w*center k+B*(w/width)≤C)
    (u : ℝ×ℝ → ℝ) (f : κ → (ℝ×ℝ) → ℂ)
    (g : ℝ×ℝ → EuclideanSpace ℂ κ) :
    normalizedSymbolSumL1 chiA chiB
      (annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity))
      topLength width (H*w) htop hwidth labels theta center
      (fun _ k => partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)) u f g =
      partitionedAnnularSumL1 psi rho beta chiA chiB topLength width w htop hwidth labels theta center u f g := by
  classical
  unfold normalizedSymbolSumL1 partitionedAnnularSumL1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with omega
  by_cases hz : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=0
  · simp only [hz,zero_mul,mul_zero,smul_zero]
  have hwindow : latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega=
      chiA (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2),
        symbolY width omega.2 (center k)) := by
    exact scaledWindow_inverse_profile_apply chiA _ width _ _
      (latticeLength_pos topLength htop labels i) hwidth omega.1 omega.2
  obtain ⟨hX,hY⟩ := hchiA _ (by simpa only [hwindow] using hz)
  obtain ⟨hVlo,hVhi⟩ := vertical_annulus_from_window w width (center k) omega.2 B c C
    hw hwidth (hlo k) (hhi k) hY
  have heq := rescaled_partitioned_symbol_eq psi rho beta A B c C a M R H hR hH hc hC ha hM hA hsmall
    hpsi hsize (latticeLength topLength labels i) w width (theta i.1 i.2) (center k) (u z)
    omega.1 omega.2 (latticeLength_pos topLength htop labels i) hw hwidth (hparam k) hX hY hVlo hVhi
  simp only [Circle.smul_def,smul_eq_mul]
  calc
    _ = (Real.fourierChar (z.1*omega.1+z.2*omega.2):ℂ)*
        (((annularCutoff (3*a/(4*(H*C))) ((M+A)/(H*c)) (by positivity) (by positivity)
          (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2)):ℂ)*
          partitionedSymbol psi (dilatedSlopeWindow rho H hH.ne') beta (H*c) (mul_pos hH hc) R hR (H*w*center k) (H*w/width)
            (symbolPoint (symbolX (latticeLength topLength labels i) omega.1 omega.2 (theta i.1 i.2))
              (symbolY width omega.2 (center k))
              (symbolU (latticeLength topLength labels i) (H*w) (u z) (theta i.1 i.2))))*
          (latticeFrequencyWindow chiA topLength width htop hwidth labels theta center i k omega*
            latticeFrequencyWindow chiB topLength width htop hwidth labels theta center i k omega*
            planarFourier (f k) omega)) := by ring
    _ = _ := by rw [heq]

end LipschitzHilbert.PacketRepresentation

end

end OAI
