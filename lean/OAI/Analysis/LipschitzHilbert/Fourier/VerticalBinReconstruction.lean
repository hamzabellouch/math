import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinEnergy
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinPlateau
import OAI.Analysis.LipschitzHilbert.Fourier.L1MultiplierLinearity

namespace OAI

/-! Exact physical reconstruction and plateau removal for the finite vertical bins. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem planarFourier_schwartz_sum {ι : Type*} (I : Finset ι)
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (omega : ℝ×ℝ) :
    planarFourier (show SchwartzMap (ℝ×ℝ) ℂ from ∑ i∈I, f i) omega=∑ i∈I, planarFourier (f i) omega := by
  have h := planarFourier_finset_sum_l1 I (fun i => f i)
    (fun i _ => (f i).integrable) omega
  have heq : (⇑(∑ i∈I, f i) : (ℝ×ℝ) → ℂ)=(fun z => ∑ i∈I, f i z) := by
    funext z
    simp only [sum_apply]
  rw [heq]
  exact h

theorem verticalBin_schwartz_reconstruction (f : SchwartzMap (ℝ×ℝ) ℂ)
    (w W c C : ℝ) (hw : 0<w) (hW : 0<W) (hc : 0<c)
    (hband : ∀ omega, planarFourier f omega≠0 → c≤w*omega.2 ∧ w*omega.2≤C) :
    (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n)
        (schwartzVerticalProjection verticalBinProfile W (verticalBinCenter ⌈C*W/w⌉₊ W n) f))=f := by
  apply planar_schwartz_ext_fourier
  intro omega
  rw [planarFourier_schwartz_sum]
  simp_rw [schwartzVerticalProjection_fourier]
  by_cases hf : planarFourier f omega=0
  · simp only [hf,mul_zero,Finset.sum_const_zero]
  · obtain ⟨hlo,hhi⟩ := hband omega hf
    have hpart := positiveBand_bin_partition w W c C omega.2 hw hW hc hlo hhi
    change (∑ n∈verticalBinLabels ⌈C*W/w⌉₊ w W c C,
      verticalBinWindow ⌈C*W/w⌉₊ W n omega.2 *
        (verticalBinWindow ⌈C*W/w⌉₊ W n omega.2 * planarFourier f omega))=planarFourier f omega
    simp_rw [←mul_assoc,←sq]
    rw [←Finset.sum_mul,hpart,one_mul]

theorem verticalBin_schwartz_plateau (f : SchwartzMap (ℝ×ℝ) ℂ) (W center : ℝ) :
    schwartzVerticalProjection verticalBinPlateau W center
      (schwartzVerticalProjection verticalBinProfile W center f)=
      schwartzVerticalProjection verticalBinProfile W center f := by
  apply planar_schwartz_ext_fourier
  intro omega
  simp only [schwartzVerticalProjection_fourier]
  rw [←mul_assoc,verticalBinPlateau_mul_profile]

end LipschitzHilbert.PacketRepresentation

end

end OAI
