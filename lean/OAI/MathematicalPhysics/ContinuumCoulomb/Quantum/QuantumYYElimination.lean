import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumYYFactor

namespace OAI

/-! The only Y-containing real two-local Pauli words are YY words. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem qmaPauliWord_zero : qmaPauliWord (fun _ : ι => 0) = 1 := by
  ext s t
  simp only [qmaPauliWord,qmaPauli_zero,Matrix.one_apply]
  by_cases h : s = t
  · subst t
    simp
  · rw [ite_eq_right h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

theorem qmaTwoLocalEvenY_cases (w : ι → Fin 4)
    (hw : (qmaPauliSupport w).card ≤ 2) (he : Even (qmaPauliYCount w)) :
    (∀ i, w i ≠ 2) ∨ ∃ i j, i ≠ j ∧ w = qmaTwoPauliWord i j 2 2 := by
  by_cases hnone : ∀ i, w i ≠ 2
  · exact Or.inl hnone
  · right
    push Not at hnone
    obtain ⟨i,hi⟩ := hnone
    let Y := Finset.univ.filter (fun k => w k = 2)
    have hsub : Y ⊆ qmaPauliSupport w := by
      intro k hk
      have h := (Finset.mem_filter.mp hk).2
      simp [qmaPauliSupport,h]
    have hpos : 0 < Y.card := Finset.card_pos.mpr ⟨i,by simp [Y,hi]⟩
    have hbound : Y.card ≤ 2 := (Finset.card_le_card hsub).trans hw
    have hcard : Y.card = 2 := by
      change Even Y.card at he
      obtain ⟨k,hk⟩ := he
      omega
    obtain ⟨a,b,hab,hY⟩ := Finset.card_eq_two.mp hcard
    have hsupport : Y = qmaPauliSupport w :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hw)
    have ha : w a = 2 := (Finset.mem_filter.mp (show a ∈ Y by rw [hY]; simp)).2
    have hb : w b = 2 := (Finset.mem_filter.mp (show b ∈ Y by rw [hY]; simp)).2
    refine ⟨a,b,hab,?_⟩
    funext k
    by_cases hka : k = a
    · simp [qmaTwoPauliWord,hka,ha]
    · by_cases hkb : k = b
      · simp [qmaTwoPauliWord,hkb,hb,Ne.symm hab]
      · have hz : w k = 0 := by
          by_contra hn
          have hk : k ∈ qmaPauliSupport w := by simp [qmaPauliSupport,hn]
          rw [← hsupport,hY] at hk
          simp [hka,hkb] at hk
        simp [qmaTwoPauliWord,hka,hkb,hz]

theorem qmaTwoLocalEvenXZFactor (w : ι → Fin 4)
    (hw : (qmaPauliSupport w).card ≤ 2) (he : Even (qmaPauliYCount w)) :
    ∃ a b : ι → Fin 4, (∀ i, a i ≠ 2) ∧ (∀ i, b i ≠ 2) ∧
      (qmaPauliSupport a).card ≤ 2 ∧ (qmaPauliSupport b).card ≤ 2 ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a := by
  rcases qmaTwoLocalEvenY_cases w hw he with h | ⟨i,j,hij,rfl⟩
  · refine ⟨w,fun _ => 0,h,by simp,hw,?_,?_,?_⟩
    · simp [qmaPauliSupport]
    · rw [qmaPauliWord_zero,Matrix.mul_one]
    · rw [qmaPauliWord_zero,Matrix.mul_one,Matrix.one_mul]
  · refine ⟨qmaTwoPauliWord i j 1 3,qmaTwoPauliWord i j 3 1,?_,?_,?_,?_,
      qmaYY_factor i j hij,qmaYY_factor_commute i j hij⟩
    · intro k
      simp only [qmaTwoPauliWord]
      split_ifs <;> decide
    · intro k
      simp only [qmaTwoPauliWord]
      split_ifs <;> decide
    · exact (Finset.card_le_card (qmaTwoPauliWord_support i j 1 3)).trans (Finset.card_insert_le _ _)
    · exact (Finset.card_le_card (qmaTwoPauliWord_support i j 3 1)).trans (Finset.card_insert_le _ _)

end ContinuumCoulomb

end

end OAI
