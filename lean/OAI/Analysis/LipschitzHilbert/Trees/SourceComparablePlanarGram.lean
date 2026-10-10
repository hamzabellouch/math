import OAI.Analysis.LipschitzHilbert.Trees.SourceRestrictedGram
import OAI.Analysis.LipschitzHilbert.Trees.SourcePlanarGramSchur

namespace OAI

/-! Comparable-scale Gram terms of actual planar vector packets are
controlled by the sum of their single-scale energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem comparable_planar_gram_energy {N : ℕ} {κ : Type*} [Fintype κ]
    (f : Fin N → κ → SchwartzMap (ℝ×ℝ) ℂ) (gap : ℕ) :
    (∑ k, ∑ i, ∑ j, if |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ) then
      (∫ z, inner ℂ (f i k z) (f j k z) ∂volume.prod volume).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*∑ i, ∑ k, ∫ z, ‖f i k z‖^2 ∂volume.prod volume := by
  have h (k : κ) := comparable_scale_gram_energy
    (fun j => (f j k).toLp 2 (volume.prod volume)) gap
  simp only [SchwartzMap.inner_toL2_toL2_eq,planar_toL2_norm_sq] at h
  calc
    _ ≤ ∑ k, ((2*gap+1:ℕ):ℝ)*∑ i, ∫ z, ‖f i k z‖^2 ∂volume.prod volume :=
      Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by rw [←Finset.mul_sum,Finset.sum_comm]

end LipschitzHilbert

end

end OAI
