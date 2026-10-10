import OAI.Analysis.LipschitzHilbert.Packets.PacketDataMaskedValue
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataDensityForest
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataJetBudget

namespace OAI

/-! The late mask normalization preserves the actual density forest,
physical packet sums and masks. Its analytic constant has an explicit
polynomial bound after the mask exponent has been chosen. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]

def PacketDensityForest.withJetControl
    {P : PacketLatticeData N κ Label Item} {packets : Finset P.PacketIndex}
    {oldSlope L a cone w tau : ℝ} {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    (forest : PacketDensityForest P packets oldSlope L a cone w tau E u)
    (scale ratio : ℝ) (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio) :
    PacketDensityForest (P.withJetControl scale ratio hratio hscale)
      packets oldSlope L a cone w tau E u where
  keepers := forest.keepers
  top := forest.top
  assigned := forest.assigned
  witness := forest.witness
  measurable := forest.measurable
  disjoint := forest.disjoint
  subset := forest.subset
  finite := forest.finite
  mass := forest.mass
  radius := forest.radius
  precision := forest.precision
  close := forest.close
  width := forest.width
  short := forest.short
  seed_short := forest.seed_short
  area := forest.area
  area_pos := forest.area_pos
  reference := forest.reference
  horizontal := forest.horizontal
  transverse := forest.transverse

@[simp] theorem withJetControl_physicalMaskedValue
    (P : PacketLatticeData N κ Label Item)
    (scale ratio : ℝ) (hratio : 1 ≤ ratio) (hscale : |scale/P.width| ≤ ratio)
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
    (v : ℝ×ℝ → ℝ) (f : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox)
    (L A : ℝ) (z : ℝ×ℝ) (q : P.PacketIndex) :
    (P.withJetControl scale ratio hratio hscale).physicalMaskedValue alt hAlt t b v f T L A z q =
      P.physicalMaskedValue alt hAlt t b v f T L A z q := rfl

theorem maskJetControl_referenceEnvelopeConstant (P : PacketLatticeData N κ Label Item)
    {L A p F cone : ℝ} (hL : 16 ≤ L) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hfactor : F*cone+2 ≤ L)
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (F*cone+2)*(P.withJetControl (4*(L^(A+2)*P.width)) (4*L^(A+2))
      (smallJetRatio_ge_one (by linarith) (by linarith))
      (P.smallJetScale_control (by linarith) P.width_pos.le (le_refl P.width))).referenceEnvelopeConstant ≤
      L^(p+2*(A+2)+2) := by
  have hLp : 0 < L := by linarith
  have h := P.smallJetControl_referenceEnvelopeConstant hL (by linarith : 0 ≤ A+2)
    P.width_pos.le (le_refl P.width) hprofile
  calc
    _ ≤ (F*cone+2)*L^(p+2*(A+2)+1) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ L*L^(p+2*(A+2)+1) := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hLp.le _)
    _ = L^(p+2*(A+2)+2) := by
      conv_lhs => lhs; rw [← Real.rpow_one L]
      rw [← Real.rpow_add hLp]
      congr 1
      ring

theorem mask_referenceEnvelopeConstant_of_ratio (P : PacketLatticeData N κ Label Item)
    {L A p F cone : ℝ} (hL : 16 ≤ L) (hA : 0 ≤ A)
    (hF : 0 ≤ F) (hcone : 0 ≤ cone) (hfactor : F*cone+2 ≤ L)
    (hratio : P.ratioBound = 4*L^(A+2))
    (hprofile : (2^P.order*P.profileBound)*3^(2*P.order) ≤ L^p) :
    (F*cone+2)*P.referenceEnvelopeConstant ≤ L^(p+2*(A+2)+2) := by
  have h := P.maskJetControl_referenceEnvelopeConstant hL hA hF hcone hfactor hprofile
  simpa only [PacketLatticeData.referenceEnvelopeConstant,withJetControl,hratio] using h

theorem PacketDensityForest.mask_geometry
    {P : PacketLatticeData N κ Label Item} {packets : Finset P.PacketIndex}
    {oldSlope L a cone w tau A : ℝ} {E : Set (ℝ×ℝ)} {u : ℝ×ℝ → ℝ}
    (forest : PacketDensityForest P packets oldSlope L a cone w tau E u)
    (hL : 1 ≤ L) (hA : a+3 ≤ A+2) :
    (∀ q ∈ packets,
      |P.actualX q.1 q.2.1 q.2.2-(forest.top (forest.assigned q)).x|+P.length q.1 ≤
        L^(A+2)*(forest.top (forest.assigned q)).length) ∧
    (∀ q ∈ packets,
      |P.actualZ q.1 q.2.1 q.2.2+(oldSlope-(forest.top (forest.assigned q)).slope)*
        P.actualX q.1 q.2.1 q.2.2-
        ((forest.top (forest.assigned q)).y-
          (forest.top (forest.assigned q)).slope*(forest.top (forest.assigned q)).x)|+P.width ≤
        L^(A+2)*(forest.top (forest.assigned q)).width) := by
  have hp := Real.rpow_le_rpow_of_exponent_le hL hA
  exact ⟨fun q hq => (forest.horizontal q hq).trans
    (mul_le_mul_of_nonneg_right hp (forest.top (forest.assigned q)).length_pos.le),
    fun q hq => (forest.transverse q hq).trans
      (mul_le_mul_of_nonneg_right hp (forest.top (forest.assigned q)).width_pos.le)⟩

end LipschitzHilbert.PacketLatticeData

end

end OAI
