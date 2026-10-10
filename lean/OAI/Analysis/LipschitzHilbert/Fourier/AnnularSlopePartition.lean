import OAI.Analysis.LipschitzHilbert.Trees.SlopePartitionGrid
import OAI.Analysis.LipschitzHilbert.Fourier.PartitionedFrequencySymbol

namespace OAI

/-! On an annular multiplier, bounded output directions imply a finite
range of frequency slopes. The constructed arithmetic partition covers
that entire range, with no remaining partition-of-unity premise. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketRepresentation

theorem annular_normalized_slope_bound (l w delta c M U u xi eta : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0<c) (hM : 0≤M)
    (hu : |u|≤U) (hfreq : |l*(xi+u*eta)|≤M) (hvertical : c≤w*eta) :
    |(-xi/eta)/(delta*(w/l))|≤U/(delta*(w/l))+M/(delta*c) := by
  have hdw : 0<delta*(w/l) := mul_pos hd (div_pos hw hl)
  have hV : 0<w*eta := hc.trans_le hvertical
  have heta : eta≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have heq : (-xi/eta)/(delta*(w/l))=
      u/(delta*(w/l))-(l*(xi+u*eta))/(delta*(w*eta)) := by
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |u/(delta*(w/l))|+|(l*(xi+u*eta))/(delta*(w*eta))| := abs_sub _ _
    _ = |u|/(delta*(w/l))+|l*(xi+u*eta)|/(delta*(w*eta)) := by
      rw [abs_div,abs_div,abs_of_pos hdw,abs_of_pos (mul_pos hd hV)]
    _ ≤ U/(delta*(w/l))+M/(delta*c) := add_le_add
      (div_le_div_of_nonneg_right hu hdw.le)
      ((div_le_div_of_nonneg_right hfreq (mul_pos hd hV).le).trans
        (div_le_div_of_nonneg_left hM (mul_pos hd hc)
          (mul_le_mul_of_nonneg_left hvertical hd.le)))

theorem finiteSlopePartition_annular (psi beta : SchwartzMap ℝ ℂ)
    (K : ℕ) (l W w delta c M U center : ℝ)
    (hl : 0<l) (hw : 0<w) (hd : 0<delta) (hc : 0<c) (hM : 0≤M)
    (hpsi : ∀ s : ℝ, psi s≠0 → |s|≤M)
    (hbeta : ∀ eta, beta (symbolY W eta center)≠0 → c≤w*eta)
    (hK : U/(delta*(w/l))+M/(delta*c)≤K)
    (u : ℝ×ℝ → ℝ) (hu : ∀ z, |u z|≤U)
    (z omega : ℝ×ℝ) (hp : psi (l*(omega.1+u z*omega.2))≠0)
    (hb : beta (symbolY W omega.2 center)≠0) :
    ∑ n : finiteSlopeLabels K, scaledSlopePartition delta hd
      (-symbolX l omega.1 omega.2 (finiteSlopeCenter K delta (w/l) n.val)/(w*omega.2))=1 := by
  have hV := hc.trans_le (hbeta omega.2 hb)
  have heta : omega.2≠0 := by intro hz; rw [hz,mul_zero] at hV; exact (lt_irrefl 0 hV)
  have hcover : |(-omega.1/omega.2)/(delta*(w/l))|≤K :=
    (annular_normalized_slope_bound l w delta c M U (u z) omega.1 omega.2
      hl hw hd hc hM (hu z) (hpsi _ hp) (hbeta _ hb)).trans hK
  have hsum := finiteSlopePartition_sum K delta (w/l) (-omega.1/omega.2) hd (div_pos hw hl) hcover
  rw [←Finset.sum_attach] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  unfold symbolX
  field_simp
  ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
