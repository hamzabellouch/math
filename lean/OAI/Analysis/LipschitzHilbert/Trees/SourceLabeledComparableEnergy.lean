import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledScaleEnergy
import OAI.Analysis.LipschitzHilbert.Trees.SourceComparablePlanarGram

namespace OAI

/-! The comparable-scale contribution for the actual labeled packet
family. Both the scale window and angular multiplicity are uniform. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def physicalScaleComponent
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (k : κ) : SchwartzMap (ℝ×ℝ) ℂ :=
  ∑ l : P.labels j, ∑ u, c j l u k • P.physicalPacket 0 j l u k

theorem physicalScaleComponent_vector
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (j : Fin N) (z : ℝ×ℝ) :
    (WithLp.toLp 2 (fun k => P.physicalScaleComponent c j k z) : EuclideanSpace ℂ κ)=
      ∑ l : P.labels j, planarFixedSynthesis (c j l) (P.physicalPacket 0 j l) z := by
  ext k
  simp only [physicalScaleComponent,WithLp.ofLp_sum,Finset.sum_apply,
    planarFixedSynthesis,sum_apply,smul_apply,smul_eq_mul]

theorem physicalScaleComponent_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (j : Fin N) :
    (∑ k, ∫ z, ‖P.physicalScaleComponent c j k z‖^2 ∂volume.prod volume)=
      ∫ z, ‖∑ l : P.labels j, planarFixedSynthesis (c j l) (P.physicalPacket 0 j l) z‖^2
        ∂volume.prod volume := by
  simp_rw [←P.physicalScaleComponent_vector c j,EuclideanSpace.norm_sq_eq]
  exact (integral_finsetSum _ (fun k _ =>
    ((P.physicalScaleComponent c j k).memLp 2 (volume.prod volume)).integrable_norm_pow
      (by decide : 2 ≠ 0))).symm

theorem physical_comparable_gram_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (gap : ℕ) (w cStar cEta CEta : ℝ) (hw : 0<w) (hcEta : 0<cEta)
    (M Q : ℕ) (hQ : 2*cStar/cEta≤Q)
    (hmultiplicity : ∀ j, SourceSlopeLabels.LocalMultiplicity Finset.univ
      (P.rowSlope j) (w/P.length j) M)
    (hspectrum : ∀ j l u k xi eta,
      planarAngularFourier (P.physicalPacket 0 j l u k) (xi,eta)≠0 →
        |xi+P.rowSlope j l*eta|≤cStar/P.length j ∧ cEta≤w*eta ∧ w*eta≤CEta) :
    (∑ k, ∑ i, ∑ j, if |(i.val:ℤ)-(j.val:ℤ)|≤(gap:ℤ) then
      (∫ z, inner ℂ (P.physicalScaleComponent c i k z)
        (P.physicalScaleComponent c j k z) ∂volume.prod volume).re else 0)≤
      ((2*gap+1:ℕ):ℝ)*(((2*Q+1)*M:ℕ):ℝ)*
        ((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ j, ∑ l : P.labels j, ∑ u, ‖c j l u‖^2*P.length j*P.width := by
  have h := comparable_planar_gram_energy (P.physicalScaleComponent c) gap
  simp_rw [P.physicalScaleComponent_energy c] at h
  calc
    _ ≤ ((2*gap+1:ℕ):ℝ)*∑ j,
        ∫ z, ‖∑ l : P.labels j, planarFixedSynthesis (c j l) (P.physicalPacket 0 j l) z‖^2
          ∂volume.prod volume := h
    _ ≤ ((2*gap+1:ℕ):ℝ)*∑ j,
        (((2*Q+1)*M:ℕ):ℝ)*((4*Real.pi)^2*P.profileBound^2*Real.pi^2)*
          ∑ l : P.labels j, ∑ u, ‖c j l u‖^2*P.length j*P.width := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum fun j _ => P.physicalPacket_local_label_scale_energy j
        (c j) w cStar cEta CEta hw hcEta M Q hQ (hmultiplicity j) (hspectrum j)
    _ = _ := by rw [←Finset.mul_sum]; ring

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
