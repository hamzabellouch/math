import OAI.Analysis.LipschitzHilbert.Estimates.PlanarFixedScaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum

namespace OAI

/-! The fixed-length energy estimate for the original physical source
packets. The profile and lattice assumptions already present in the
source family discharge every envelope and overlap hypothesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem physicalPlanarPacket_profile_envelope (f : SchwartzMap (ℝ×ℝ) ℂ)
    (n : ℕ) (a b l W theta frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) (z : ℝ×ℝ) :
    ‖physicalPlanarPacket f a b l W theta frequency hl hW z‖ ≤
      planarProfileConstant f n *
        (lineEnvelope a l n z.1 * lineEnvelope (b-theta*a) W n (z.2-theta*z.1)) := by
  rw [physicalPlanarPacket_apply,norm_mul]
  have hphase : ‖Complex.exp ((frequency*((z.2-b)-theta*(z.1-a)):ℝ)*Complex.I)‖ = 1 := by
    simp [Complex.norm_exp]
  rw [hphase,one_mul]
  have h := planar_profile_base_envelope f n 0
    ((z.1-a)/l,((z.2-b)-theta*(z.1-a))/W)
  have hy : ((z.2-b)-theta*(z.1-a))/W =
      ((z.2-theta*z.1)-(b-theta*a))/W := by ring
  simpa only [planarVerticalJet,ite_true,lineEnvelope,sub_zero,div_one,hy] using h

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

theorem physicalPacket_lattice_envelope (P : SourceLatticePacket N κ ι)
    (t : ℝ) (j : Fin N) (u : ι j) (k : κ) (z : ℝ×ℝ) :
    ‖P.physicalPacket t j u k z‖ ≤ P.profileBound *
      (lineEnvelope (P.originX j+P.length j*(P.site j u).1) (P.length j) 1 z.1 *
        lineEnvelope (P.originZ j-P.rowSlope j*P.originX j+P.width*(P.site j u).2)
          P.width 1 (z.2-(t+P.rowSlope j)*z.1)) := by
  have h := physicalPlanarPacket_profile_envelope (P.profile j u k) (2*P.order)
    (P.actualX j u) (P.actualZ j u+t*P.actualX j u) (P.length j) P.width
    (t+P.rowSlope j) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne' z
  have horder : 1 ≤ 2*P.order := by have := P.order_ge_three; omega
  have hcenter : P.actualZ j u+t*P.actualX j u-(t+P.rowSlope j)*P.actualX j u =
      P.originZ j-P.rowSlope j*P.originX j+P.width*(P.site j u).2 := by
    simp only [actualX,actualZ]
    ring
  rw [hcenter] at h
  apply h.trans
  apply mul_le_mul (P.profile_bound j u k)
  · exact mul_le_mul
      (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
      (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  · exact mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)
  · exact P.profileBound_pos.le

theorem physicalPacket_scale_energy (P : SourceLatticePacket N κ ι)
    (t : ℝ) (j : Fin N) (c : ι j → EuclideanSpace ℂ κ) :
    (∫ z, ‖planarFixedSynthesis c (P.physicalPacket t j) z‖^2 ∂volume.prod volume) ≤
      ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
        ∑ u, ‖c u‖^2*P.length j*P.width := by
  exact planar_fixed_scale_energy c (P.physicalPacket t j) (P.site j) (P.site_injective j)
    (P.originX j) (P.originZ j-P.rowSlope j*P.originX j) (P.length j) P.width
    (t+P.rowSlope j) P.profileBound (P.length_pos j) P.width_pos
    (fun u k z => P.physicalPacket_lattice_envelope t j u k z)

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
