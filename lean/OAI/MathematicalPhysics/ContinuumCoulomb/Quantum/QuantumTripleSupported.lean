import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliTripleSplit

namespace OAI

/-! The three factors can be chosen inside the original Pauli support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaPauliWord_triple_supported (w : ι → Fin 4) (hw : (qmaPauliSupport w).card ≤ 3)
    (he : Even (qmaPauliYCount w)) :
    ∃ a b c : ι → Fin 4,
      qmaPauliSupport a ⊆ qmaPauliSupport w ∧
      qmaPauliSupport b ⊆ qmaPauliSupport w ∧
      qmaPauliSupport c ⊆ qmaPauliSupport w ∧
      (qmaPauliSupport a).card ≤ 1 ∧ (qmaPauliSupport b).card ≤ 1 ∧ (qmaPauliSupport c).card ≤ 1 ∧
      qmaPauliWord a*qmaPauliWord b*qmaPauliWord c = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a ∧
      qmaPauliWord a*qmaPauliWord c = qmaPauliWord c*qmaPauliWord a ∧
      qmaPauliWord b*qmaPauliWord c = qmaPauliWord c*qmaPauliWord b ∧
      decide (Odd (qmaPauliYCount a)) = decide (Odd (qmaPauliYCount b)) ∧
      Even (qmaPauliYCount c) := by
  obtain ⟨P,C,hP,hC,hPC,hcover,hnoY⟩ := qmaThreeSupport_split w hw he
  obtain ⟨L,T,hL,hT,hLT,hunion⟩ := qmaBalancedSupport P 1 (by omega)
  have hLP : L ⊆ P := by rw [← hunion]; exact Finset.subset_union_left
  have hTP : T ⊆ P := by rw [← hunion]; exact Finset.subset_union_right
  let a := qmaPauliRestrict L w
  let b := qmaPauliRestrict T w
  let c := qmaPauliRestrict C w
  let v := qmaPauliRestrict P w
  have hc : qmaPauliYCount c = 0 := by
    apply qmaPauliYCount_zero
    intro i
    by_cases hi : i ∈ C
    · simpa only [c,qmaPauliRestrict,hi,ite_true] using hnoY i hi
    · simp [c,qmaPauliRestrict,hi]
  have hvcover : qmaPauliSupport v ⊆ L ∪ T := by
    rw [hunion]
    exact qmaPauliRestrict_support P w
  have hv : Even (qmaPauliYCount v) := by
    have hs := qmaPauliYCount_split P C w hPC (by rw [hcover])
    change qmaPauliYCount v+qmaPauliYCount c = qmaPauliYCount w at hs
    rw [hc,add_zero] at hs
    rwa [hs]
  have hab : qmaPauliWord a*qmaPauliWord b = qmaPauliWord v := by
    have h := qmaPauliRestrict_factor L T v hLT hvcover
    simpa only [v,qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] using h
  have hPS : P ⊆ qmaPauliSupport w := by rw [←hcover]; exact Finset.subset_union_left
  have hCS : C ⊆ qmaPauliSupport w := by rw [←hcover]; exact Finset.subset_union_right
  refine ⟨a,b,c,(qmaPauliRestrict_support L w).trans (hLP.trans hPS),
    (qmaPauliRestrict_support T w).trans (hTP.trans hPS),
    (qmaPauliRestrict_support C w).trans hCS,(Finset.card_le_card (qmaPauliRestrict_support L w)).trans hL,
    (Finset.card_le_card (qmaPauliRestrict_support T w)).trans hT,
    (Finset.card_le_card (qmaPauliRestrict_support C w)).trans hC,?_,
    qmaPauliRestrict_commute L T w hLT,
    qmaPauliRestrict_commute L C w (hPC.mono_left hLP),
    qmaPauliRestrict_commute T C w (hPC.mono_left hTP),?_,?_⟩
  · rw [hab]
    exact qmaPauliRestrict_factor P C w hPC (by rw [hcover])
  · have h := qmaPauliRestrict_same_parity L T v hLT hvcover hv
    simpa only [v,qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] using h
  · rw [hc]
    norm_num


end ContinuumCoulomb

end

end OAI
