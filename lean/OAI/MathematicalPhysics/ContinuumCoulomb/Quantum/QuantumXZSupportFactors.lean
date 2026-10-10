import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYElimination
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZTriple

namespace OAI

/-! X/Z factorizations can be chosen inside the original Pauli support. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem qmaTwoPauliYY_support_eq (i j : ι) :
    qmaPauliSupport (qmaTwoPauliWord i j 2 2) = {i,j} := by
  ext k
  simp only [qmaPauliSupport,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp [qmaTwoPauliWord,hki,hkj]

theorem qmaTwoLocalEvenXZ_supported (w : ι → Fin 4)
    (hw : (qmaPauliSupport w).card ≤ 2) (he : Even (qmaPauliYCount w)) :
    ∃ a b : ι → Fin 4, qmaPauliSupport a ⊆ qmaPauliSupport w ∧
      qmaPauliSupport b ⊆ qmaPauliSupport w ∧ (∀ i, a i ≠ 2) ∧ (∀ i, b i ≠ 2) ∧
      (qmaPauliSupport a).card ≤ 2 ∧ (qmaPauliSupport b).card ≤ 2 ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a := by
  rcases qmaTwoLocalEvenY_cases w hw he with h | ⟨i,j,hij,rfl⟩
  · refine ⟨w,fun _ => 0,Finset.Subset.refl _,by simp [qmaPauliSupport],h,by simp,hw,?_,?_,?_⟩
    · simp [qmaPauliSupport]
    · rw [qmaPauliWord_zero,Matrix.mul_one]
    · rw [qmaPauliWord_zero,Matrix.mul_one,Matrix.one_mul]
  · refine ⟨qmaTwoPauliWord i j 1 3,qmaTwoPauliWord i j 3 1,
      (qmaTwoPauliWord_support i j 1 3).trans_eq (qmaTwoPauliYY_support_eq i j).symm,
      (qmaTwoPauliWord_support i j 3 1).trans_eq (qmaTwoPauliYY_support_eq i j).symm,?_,?_,?_,?_,
      qmaYY_factor i j hij,qmaYY_factor_commute i j hij⟩
    · intro k
      simp only [qmaTwoPauliWord]
      split_ifs <;> decide
    · intro k
      simp only [qmaTwoPauliWord]
      split_ifs <;> decide
    · exact (Finset.card_le_card (qmaTwoPauliWord_support i j 1 3)).trans (Finset.card_insert_le _ _)
    · exact (Finset.card_le_card (qmaTwoPauliWord_support i j 3 1)).trans (Finset.card_insert_le _ _)


theorem qmaXZTriple_supported (w : ι → Fin 4) (hw : (qmaPauliSupport w).card ≤ 3)
    (hy : ∀ i, w i ≠ 2) :
    ∃ a b c v : ι → Fin 4,
      qmaPauliSupport a ⊆ qmaPauliSupport w ∧ qmaPauliSupport b ⊆ qmaPauliSupport w ∧
      qmaPauliSupport c ⊆ qmaPauliSupport w ∧ qmaPauliSupport v ⊆ qmaPauliSupport w ∧
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
  have hPS : P ⊆ qmaPauliSupport w := by rw [←hcover]; exact Finset.subset_union_left
  have hCS : C ⊆ qmaPauliSupport w := by rw [←hcover]; exact Finset.subset_union_right
  refine ⟨qmaPauliRestrict L w,qmaPauliRestrict T w,qmaPauliRestrict C w,
    qmaPauliRestrict P w,(qmaPauliRestrict_support L w).trans (hLP.trans hPS),
    (qmaPauliRestrict_support T w).trans (hTP.trans hPS),
    (qmaPauliRestrict_support C w).trans hCS,(qmaPauliRestrict_support P w).trans hPS,
    qmaPauliRestrict_noY _ _ hy,qmaPauliRestrict_noY _ _ hy,
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
