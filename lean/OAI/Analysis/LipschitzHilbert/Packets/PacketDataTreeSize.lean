import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSizeTest

namespace OAI

/-! The actual unsigned size test supplies the separated energy of
a spatial piece in arbitrary reference coordinates. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)

theorem reference_separated_energy_eq_sizeTest
    (Q : Finset P.PacketIndex) (t w cb : ℝ) (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox)
    (ht : T.slope=t)
    (hlen : ∀ q∈Q, P.length q.1≤T.length)
    (hcenter : ∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2))
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1)) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)=
      P.unsignedSizeTestEnergy w cb cell grid c Q T := by
  unfold unsignedSizeTestEnergy
  apply Finset.sum_congr rfl
  intro q hq
  simp only [hlen q hq,hcenter q hq,ht,abs_sub_comm,hangle q hq,true_and]

theorem reference_selected_size_bound
    (Q R : Finset P.PacketIndex) (hQR : Q⊆R) (t w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (T : SlopeBox)
    (ht : T.slope=t) (hwidth : T.width=P.width) (htime : T.length≤tau)
    (hlen : ∀ q∈Q, P.length q.1≤T.length)
    (hcenter : ∀ q∈Q, (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2))
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hsize : ∀ U : SlopeBox, U.width=P.width → U.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R U≤sigma^2*U.area) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)≤sigma^2*T.area := by
  rw [P.reference_separated_energy_eq_sizeTest Q t w cb cell grid c T ht hlen hcenter hangle]
  exact (P.unsignedSizeTestEnergy_mono w cb cell grid c hQR T).trans (hsize T hwidth htime)

def referenceTreeTop (t a b : ℝ) : SlopeBox where
  x := a
  y := b+t*a
  slope := t
  length := P.topLength
  width := P.width
  length_pos := P.topLength_pos
  width_pos := P.width_pos

/-- Global size control supplies precisely the separated energy bound
needed on each centered spatial piece. -/
theorem reference_piece_size_bound
    (Q R : Finset P.PacketIndex) (hQR : Q⊆R) (t a b w cb tau sigma : ℝ)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (htime : P.topLength≤tau)
    (hX : ∀ q∈Q, |P.actualX q.1 q.2.1 q.2.2-a|≤P.topLength/2)
    (hY : ∀ q∈Q, |P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b|≤P.width/2)
    (hangle : ∀ q∈Q, t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1))
    (hsize : ∀ U : SlopeBox, U.width=P.width → U.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R U≤sigma^2*U.area) :
    (∑ q∈Q, if cb*w/P.length q.1≤|P.rowSlope q.1 q.2.1-t| then
      ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width else 0)≤sigma^2*(P.topLength*P.width) := by
  apply P.reference_selected_size_bound Q R hQR t w cb tau sigma cell grid c
    (P.referenceTreeTop t a b) rfl rfl htime _ _ hangle hsize
  · intro q _
    exact div_le_self P.topLength_pos.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  · intro q hq
    change |P.actualX q.1 q.2.1 q.2.2-a|≤(1/2:ℝ)*P.topLength ∧
      |(P.actualZ q.1 q.2.1 q.2.2-(b+t*a))-t*(P.actualX q.1 q.2.1 q.2.2-a)|≤(1/2:ℝ)*P.width
    constructor
    · linarith [hX q hq]
    · have he : (P.actualZ q.1 q.2.1 q.2.2-(b+t*a))-t*(P.actualX q.1 q.2.1 q.2.2-a)=
          P.actualZ q.1 q.2.1 q.2.2-t*P.actualX q.1 q.2.1 q.2.2-b := by ring
      rw [he]
      linarith [hY q hq]

end LipschitzHilbert.PacketLatticeData

end

end OAI
