import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedLattice
import OAI.Analysis.LipschitzHilbert.Trees.SourceCarrierFreeEnvelope

namespace OAI

/-! Carrier-free raw bounds for the original labeled lattices, before
any bound on the total number of labels is imposed. -/

noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

def absoluteConstant : ℝ :=
  ((2^P.order*P.profileBound)*P.ratioBound^2)*3^(2*P.order)

theorem absoluteConstant_pos : 0 < P.absoluteConstant := by
  have hR : 0 < P.ratioBound := zero_lt_one.trans_le P.ratioBound_ge_one
  have hB := P.profileBound_pos
  unfold absoluteConstant
  positivity

def snappedSite (j : Fin N) (l : P.labels j) (u : Item j l) : ℤ×ℤ :=
  snappedLatticeSite (P.originX j l) (P.originZ j l) (P.length j) P.width
    (P.rowSlope j l) (P.site j l u)

theorem snappedSite_injective (j : Fin N) (l : P.labels j) :
    Function.Injective (P.snappedSite j l) :=
  (snappedLatticeSite_injective _ _ _ _ _).comp (P.site_injective j l)

theorem raw_swapped_joint_measurable (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) :
    Measurable (fun z : ℝ×ℝ => P.raw i j l u k z.2 z.1) := by
  have hm : Measurable (fun z : ℝ×ℝ => P.raw i j l u k z.1 z.2) :=
    (modulatedPlanarJet_continuous (P.profile j l u k) (P.actualX j l u) (P.actualZ j l u)
      (P.length j) P.width (-P.rowSlope j l) (P.frequency k) P.scale
      (P.length_pos j).ne' i).measurable
  intro s hs
  change MeasurableSet (Prod.swap ⁻¹' ((fun z : ℝ×ℝ => P.raw i j l u k z.1 z.2) ⁻¹' s))
  exact (measurable_swap : Measurable (Prod.swap : ℝ×ℝ → ℝ×ℝ)) (hm hs)

theorem raw_absolute_envelope (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y x : ℝ) :
    ‖P.raw i j l u k y x‖ ≤ ((2^P.order*P.profileBound)*P.ratioBound^2)*
      (lineEnvelope (P.actualX j l u) (P.length j) P.order x*
        lineEnvelope (P.actualZ j l u) P.width P.order y) := by
  let C := P.ratioBound^2*P.profileBound
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) P.profileBound_pos.le
  have hprofile : ∀ z, ‖planarProfileJet (P.profile j l u k) (P.scale/P.width) i z‖ ≤ C*
      (lineEnvelope 0 1 (2*P.order) z.1*lineEnvelope 0 1 (2*P.order) z.2) := by
    intro z
    exact (planar_profile_envelope (P.profile j l u k) (2*P.order) (P.scale/P.width)
      P.ratioBound P.ratioBound_ge_one P.scale_bound i z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (P.profile_bound j l u k) (sq_nonneg _))
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have hshear : |(-P.rowSlope j l)*P.length j/P.width| ≤ 1 := by
    simpa only [length,neg_mul,neg_div,abs_neg] using P.shear_bound j l
  have h := modulatedPlanarSlice_envelope (planarProfileJet (P.profile j l u k) (P.scale/P.width) i)
    (P.actualX j l u) (P.actualZ j l u) (P.length j) P.width (-P.rowSlope j l) (P.frequency k)
    y C (P.length_pos j).ne' P.order hC hshear hprofile x
  convert h using 1 <;> simp only [raw,modulatedPlanarJet,div_eq_mul_inv,C]
  ring

theorem raw_absolute_tileEnvelope (horder : 6 ≤ P.order) (i : Fin 3)
    (j : Fin N) (l : P.labels j) (u : Item j l) (k : κ) (z : ℝ×ℝ) :
    ‖P.raw i j l u k z.2 z.1‖ ≤ P.absoluteConstant*
      tileEnvelope (P.length j*(P.snappedSite j l u).1)
        (P.width*(P.snappedSite j l u).2) (P.length j) P.width 6 z := by
  have hs := snappedLatticeSite_envelope (P.originX j l) (P.originZ j l) (P.length j)
    P.width (P.rowSlope j l) z.1 z.2 (P.length_pos j) P.width_pos (P.site j l u) P.order P.order
  have hp : (3:ℝ)^P.order*3^P.order = 3^(2*P.order) := by
    rw [← pow_add]
    congr 1
    omega
  have hA : 0 ≤ (2^P.order*P.profileBound)*P.ratioBound^2 := by
    have := P.profileBound_pos
    positivity
  have hs' := mul_le_mul_of_nonneg_left hs hA
  rw [hp] at hs'
  have hraw := (P.raw_absolute_envelope i j l u k z.2 z.1).trans hs'
  apply hraw.trans
  change ((2^P.order*P.profileBound)*P.ratioBound^2)*
    (3^(2*P.order)*(lineEnvelope _ _ P.order z.1*lineEnvelope _ _ P.order z.2)) ≤ _
  rw [← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ P.absoluteConstant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
    (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)

theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (l : P.labels j)
    (u : Item j l) (k : κ) (y t : ℝ) :
    P.raw i j l u k y = planarSchwartzSlice
      (planarCovariantJet (P.physicalPacket t j l u k) (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j l u k) (P.actualX j l u)
    (P.actualZ j l u+t*P.actualX j l u) (P.length j) P.width
    (t+P.rowSlope j l) (P.frequency k) P.scale y t (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j l u+t*P.actualX j l u-t*P.actualX j l u = P.actualZ j l u := by ring
  have hd : t-(t+P.rowSlope j l) = -P.rowSlope j l := by ring
  simpa only [hc,hd,raw,physicalPacket] using h.symm

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
