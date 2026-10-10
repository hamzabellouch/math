import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPauliTripleSplit

namespace OAI

/-! Disjoint single-site X/Z factors, retaining their explicit two-site product. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaPauliRestrict_noY (S : Finset ι) (w : ι → Fin 4) (hw : ∀ i, w i ≠ 2) :
    ∀ i, qmaPauliRestrict S w i ≠ 2 := by
  intro i
  simp only [qmaPauliRestrict]
  split_ifs
  · exact hw i
  · decide

theorem qmaXZTripleFactor (w : ι → Fin 4) (hw : (qmaPauliSupport w).card ≤ 3)
    (hy : ∀ i, w i ≠ 2) :
    ∃ a b c v : ι → Fin 4,
      (∀ i, a i ≠ 2) ∧ (∀ i, b i ≠ 2) ∧ (∀ i, c i ≠ 2) ∧ (∀ i, v i ≠ 2) ∧
      (qmaPauliSupport a).card ≤ 1 ∧ (qmaPauliSupport b).card ≤ 1 ∧
      (qmaPauliSupport c).card ≤ 1 ∧ (qmaPauliSupport v).card ≤ 2 ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord v ∧
      qmaPauliWord v*qmaPauliWord c = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a ∧
      qmaPauliWord a*qmaPauliWord c = qmaPauliWord c*qmaPauliWord a ∧
      qmaPauliWord b*qmaPauliWord c = qmaPauliWord c*qmaPauliWord b := by
  have he : Even (qmaPauliYCount w) := by rw [qmaPauliYCount_zero w hy]; norm_num
  obtain ⟨P,C,hP,hC,hPC,hcover,_⟩ := qmaThreeSupport_split w hw he
  obtain ⟨L,T,hL,hT,hLT,hunion⟩ := qmaBalancedSupport P 1 (by omega)
  have hLP : L ⊆ P := by rw [← hunion]; exact Finset.subset_union_left
  have hTP : T ⊆ P := by rw [← hunion]; exact Finset.subset_union_right
  refine ⟨qmaPauliRestrict L w,qmaPauliRestrict T w,qmaPauliRestrict C w,
    qmaPauliRestrict P w,qmaPauliRestrict_noY _ _ hy,qmaPauliRestrict_noY _ _ hy,
    qmaPauliRestrict_noY _ _ hy,qmaPauliRestrict_noY _ _ hy,
    (Finset.card_le_card (qmaPauliRestrict_support L w)).trans hL,
    (Finset.card_le_card (qmaPauliRestrict_support T w)).trans hT,
    (Finset.card_le_card (qmaPauliRestrict_support C w)).trans hC,
    (Finset.card_le_card (qmaPauliRestrict_support P w)).trans hP,?_,?_,
    qmaPauliRestrict_commute L T w hLT,
    qmaPauliRestrict_commute L C w (hPC.mono_left hLP),
    qmaPauliRestrict_commute T C w (hPC.mono_left hTP)⟩
  · have h := qmaPauliRestrict_factor L T (qmaPauliRestrict P w) hLT
      (by rw [hunion]; exact qmaPauliRestrict_support P w)
    simpa only [qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] using h
  · exact qmaPauliRestrict_factor P C w hPC (by rw [hcover])

end ContinuumCoulomb

end

end OAI
