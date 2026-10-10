import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedSum
import OAI.Analysis.LipschitzHilbert.Packets.PacketDataSelectedPrefix

namespace OAI

/-! The selected reference lattice preserves every scale partial sum,
its interval maximum, and its exact coefficient energy. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.PacketLatticeData
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : PacketLatticeData N κ Label Item)
  (S : Finset P.PacketIndex) (t Cb w F : ℝ) (hw : 0<w) (hCb : 0≤Cb) (hF : 0≤F)
  (hwide : Cb*w≤P.width) (hfrequency : ∀ k, |P.frequency k|≤F/w)
  (hnear : ∀ q∈S, |P.rowSlope q.1 q.2.1-t|≤Cb*w/P.length q.1)
local notation "Q" => P.selectedReference S t Cb w F hw hCb hF hwide hfrequency hnear

theorem selectedReference_partial
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (n : ℕ) (z : ℝ×ℝ) :
    (Q).physicalTreePartial t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c) n z =
      P.physicalTreePartial 0 (P.onPackets S c) n z := by
  have hs := P.selectedReference_synthesis S t Cb w F hw hCb hF hwide hfrequency hnear c
    (fun j _ _ => if j.val<n then 1 else 0) z
  have hleft : (Q).physicalTreePartial t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c) n z =
      (Q).physicalTreeSelectorValue t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c)
      (P.selectedMultipliers S t Cb w F hw hCb hF hwide hfrequency hnear
        (fun j _ _ => if j.val<n then 1 else 0)) z := by
    ext k
    simp only [SourceLabeledLattice.physicalTreePartial,packetPartialSum,
      SourceLabeledLattice.physicalTreeSelectorValue,WithLp.ofLp_sum,Finset.sum_apply,
      planarFixedSynthesis,selectedMultipliers,Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val<n
    · simp only [hj,ite_true,mul_one]
    · simp only [hj,ite_false,WithLp.ofLp_zero,Pi.zero_apply,mul_zero,zero_mul,
        Finset.sum_const_zero]
  rw [hleft,hs,P.selected_partial_eq]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hj : q.1.val<n
  · simp only [hj,ite_true,mul_one,packetVector]
  · simp only [hj,ite_false,mul_zero,zero_mul]
    rfl

theorem selectedReference_maximal
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) (z : ℝ×ℝ) :
    (Q).physicalTreeMaximal t
      (P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c) z =
      P.physicalTreeMaximal 0 (P.onPackets S c) z := by
  unfold SourceLabeledLattice.physicalTreeMaximal physicalTreeMaximal
  congr 1
  funext n
  exact P.selectedReference_partial S t Cb w F hw hCb hF hwide hfrequency hnear c n z

theorem selectedReference_energy
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ) :
    (∑ j, ∑ l : (Q).labels j, ∑ v : P.SelectedItem S j l,
      ‖P.selectedCoefficients S t Cb w F hw hCb hF hwide hfrequency hnear c j l v‖^2*
        (Q).length j*(Q).width)=
      ∑ q∈S, ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width := by
  have h := P.selectedReference_sum S t Cb w F hw hCb hF hwide hfrequency hnear
    (fun q => ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width)
  simp only [Fintype.sum_sigma] at h
  exact h

end LipschitzHilbert.PacketLatticeData

end

end OAI
