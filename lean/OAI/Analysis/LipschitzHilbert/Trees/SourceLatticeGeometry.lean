import OAI.Analysis.LipschitzHilbert.Packets.SourceLatticePacket

namespace OAI

/-! Actual-center localization supplies the top geometry after snapping.
The full one-mesh displacement is retained in each hypothesis. -/

noncomputable section
namespace LipschitzHilbert.SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)

theorem family_centerX_error (j : Fin N) (u : ι j) :
    |P.actualX j u-P.family.centerX j u| ≤ P.length j := by
  simpa only [actualX,family_centerX,snappedSite] using
    snappedLatticeSite_horizontal (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) (P.length_pos j) (P.site j u)

theorem family_centerZ_error (j : Fin N) (u : ι j) :
    |P.actualZ j u-P.family.centerZ j u| ≤ P.width := by
  simpa only [actualZ,family_centerZ,snappedSite] using
    snappedLatticeSite_vertical (P.originX j) (P.originZ j) (P.length j)
      P.width (P.rowSlope j) P.width_pos (P.site j u)

theorem family_centerX_local (j : Fin N) (u : ι j) (x R : ℝ)
    (hloc : |P.actualX j u-x|+P.length j ≤ R) :
    |P.family.centerX j u-x| ≤ R := by
  calc
    _ ≤ |P.family.centerX j u-P.actualX j u|+|P.actualX j u-x| := abs_sub_le _ _ _
    _ ≤ P.length j+|P.actualX j u-x| := by
      gcongr
      simpa only [abs_sub_comm] using P.family_centerX_error j u
    _ ≤ R := by linarith

theorem family_centerZ_local (j : Fin N) (u : ι j) (y R : ℝ)
    (hloc : |P.actualZ j u-y|+P.width ≤ R) :
    |P.family.centerZ j u-y| ≤ R := by
  calc
    _ ≤ |P.family.centerZ j u-P.actualZ j u|+|P.actualZ j u-y| := abs_sub_le _ _ _
    _ ≤ P.width+|P.actualZ j u-y| := by
      gcongr
      simpa only [abs_sub_comm] using P.family_centerZ_error j u
    _ ≤ R := by linarith

end LipschitzHilbert.SourceLatticePacket

end

end OAI
