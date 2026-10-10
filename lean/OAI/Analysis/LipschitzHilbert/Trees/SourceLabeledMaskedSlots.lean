import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainSlots
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlottedCoefficient

namespace OAI

/-! Masked centered synthesis in the original labeled family is the
exact sum of its fixed-slot syntheses. In particular the cubic variation
is controlled by the actual centered masked variations already bounded
on physical intervals. No total-label factor occurs. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
  (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
  (t a : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)
  (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
  (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ)

def physicalCenteredMaskedBand (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  WithLp.toLp 2 (fun k => ∑ l : P.labels j, ∑ u : Item j l,
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))

def physicalCenteredMaskedVariation (x : ℝ) : ℝ :=
  cubicVariation (packetPartialSum
    (fun j => P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x)) N

theorem physicalCenteredMaskedBand_continuous (j : Fin N) :
    Continuous (P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hline : Continuous (fun x : ℝ => (x,y+t*x)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hline))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hline)

theorem physicalCenteredMaskedVariation_continuous :
    Continuous (P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredMaskedBand_continuous alt hAlt t a b v g T L A y j
  · simp only [ite_eq_right hj]
    exact continuous_const

/-- Joint continuity in the original physical point, before selecting
a reference line or interval. -/
theorem physicalCenteredMaskedBand_physical_continuous (j : Fin N) :
    Continuous (fun z : ℝ×ℝ => P.physicalCenteredMaskedBand
      alt hAlt t a b v g T L A (z.2-t*z.1) j z.1) := by
  apply (PiLp.continuous_toLp 2 (fun _ : κ => ℂ)).comp
  apply continuous_pi
  intro k
  apply continuous_finsetSum
  intro l _
  apply continuous_finsetSum
  intro u _
  have hpoint : Continuous (fun z : ℝ×ℝ => (z.1,(z.2-t*z.1)+t*z.1)) := by fun_prop
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (((T j l u).mask_continuous L A).comp hpoint))).mul
    (((P.withProfile alt hAlt).physicalPacket t j l u k).continuous.comp hpoint)

theorem physicalCenteredMaskedVariation_physical_continuous :
    Continuous (fun z : ℝ×ℝ => P.physicalCenteredMaskedVariation
      alt hAlt t a b v g T L A (z.2-t*z.1) z.1) := by
  apply continuous_cubicVariation _ _ N
  intro n
  apply continuous_finsetSum
  intro j _
  by_cases hj : j.val < n
  · simpa only [ite_eq_left hj] using
      P.physicalCenteredMaskedBand_physical_continuous alt hAlt t a b v g T L A j
  · simp only [ite_eq_right hj]
    exact continuous_const

variable {B : ℕ} (hcard : ∀ j, (P.labels j).card ≤ B)
  (hb : ∀ j l k, ‖b j l k t‖ ≤ 1)

/-- The slot functions use the original alternate packet and original
mask at each retained item. -/
def slotCenteredMaskedBand (s : Fin B) (j : Fin N) (x : ℝ) : EuclideanSpace ℂ κ :=
  (P.slotted hcard s).physicalCenteredMaskedBand
    (fun j p k => b j p.1.1 k t)
    (P.slottedAlt hcard alt s) (P.slottedAlt_bound hcard alt hAlt s)
    (fun j => a*(2:ℝ)^j.val) v g
    (fun j p => T j p.1.1 p.1.2) L A t y j x

include hb in
theorem slotCenteredMaskedBand_apply (s : Fin B) (j : Fin N) (x : ℝ) (k : κ) :
    P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x k =
      ∑ p : P.SlotItem hcard s j,
        P.physicalFrozenCenteredCoefficient t a b v g j p.1.1 p.1.2 k*
          ((T j p.1.1 p.1.2).mask L A (x,y+t*x):ℂ)*
          (P.withProfile alt hAlt).physicalPacket t j p.1.1 p.1.2 k (x,y+t*x) := by
  have h := (P.slotted hcard s).physicalCenteredMaskedBand_eq_frozen
    (fun j p k => b j p.1.1 k t) (fun j p k => hb j p.1.1 k)
    (P.slottedAlt hcard alt s) (P.slottedAlt_bound hcard alt hAlt s)
    (fun j => a*(2:ℝ)^j.val) v g (fun j p => T j p.1.1 p.1.2) L A t y j x
  have he := congrArg (fun z : EuclideanSpace ℂ κ => z k) h
  change P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x k = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro p _
  have hc := congrArg (fun z : EuclideanSpace ℂ κ => z k)
    (P.frozenSlot_physicalCenteredCoefficient hcard t a b hb v g s j p)
  change ((P.slotted hcard s).frozenProfile (fun j p k => b j p.1.1 k t)
    (fun j p k => hb j p.1.1 k)).physicalCenteredCoefficient t t
      (fun j => a*(2:ℝ)^j.val) v g j p k = _ at hc
  rw [hc,P.slotted_alt_physicalPacket hcard alt hAlt]

include hb in
/-- Exact synthesis recombination, prior to taking any norm. -/
theorem physicalCenteredMaskedBand_eq_slots (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      ∑ s : Fin B, P.slotCenteredMaskedBand alt hAlt t a b v g T L A y hcard s j x := by
  ext k
  have hsum := P.sum_slotted (E := ℂ) hcard j
    (fun l u => P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x))
  simp only [physicalCenteredMaskedBand,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]
  simp_rw [P.slotCenteredMaskedBand_apply alt hAlt t a b v g T L A y hcard hb]
  exact hsum.symm

include hb in
/-- Cubic variation is taken only after restoring the original labeled
packet sum, and costs the fixed sum of slot variations. -/
theorem physicalCenteredMaskedVariation_le_slots (x : ℝ) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x ≤
      ∑ s : Fin B, cubicVariation
        (packetPartialSum (fun j => P.slotCenteredMaskedBand
          alt hAlt t a b v g T L A y hcard s j x)) N := by
  unfold physicalCenteredMaskedVariation
  simp_rw [P.physicalCenteredMaskedBand_eq_slots alt hAlt t a b v g T L A y hcard hb]
  exact source_slot_packet_variation_le _

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
