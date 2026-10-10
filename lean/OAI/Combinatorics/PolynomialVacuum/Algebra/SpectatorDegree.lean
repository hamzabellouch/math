import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectatorFiltration
import OAI.Combinatorics.PolynomialVacuum.Algebra.MarkedDegree

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem omitPair_spectatorSlot {n : ℕ} (i : Fin (n+1)) (l : Fin n) :
    spectatorSlot (i.succAbove l) (pairRight i)=omitPair i l := by
  by_cases h : l.val < i.val
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]
    apply Fin.ext
    simp [spectatorSlot,pairRight,omitPair,h,show l.val < i.val+1 by omega]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show i≤l.castSucc from Nat.le_of_not_gt h)]
    apply Fin.ext
    simp [spectatorSlot,pairRight,omitPair,h,show ¬l.val+1 < i.val+1 by omega]

theorem rightSpectators_count {n : ℕ} (i j : Fin (n+1)) :
    (rightSpectators i).count j=if i<j then 1 else 0 := by
  have hn : (rightSpectators i).Nodup := (List.nodup_finRange (n+1)).filter _
  by_cases h : i<j
  · rw [ite_eq_left h]
    simp [rightSpectators,h]
  · rw [ite_eq_right h]
    apply List.count_eq_zero.mpr
    simp [rightSpectators,h]

theorem leftFusionFactors_spectator_degree {n : ℕ} (i j : Fin (n+1)) (hji : j≠i) :
    (leftFusionFactors i).degreeOf j ≤ if j < i then 2 else 0 := by
  apply (degreeOf_prod_le _ _ _).trans
  calc
    _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin (n+1) => k < i), if k=j then 2 else 0 := by
      apply Finset.sum_le_sum
      intro k hk
      have hfactor (c : ℂ) : (X k-C c*X i : MvPolynomial (Fin (n+1)) ℂ).degreeOf j ≤ if k=j then 1 else 0 := by
        rw [sub_eq_add_neg]
        have hi : (- (C c*X i) : MvPolynomial (Fin (n+1)) ℂ).degreeOf j≤0 := by
          rw [degreeOf_neg]; exact dconst_mul _ (le_of_eq (degreeOf_X_of_ne hji))
        by_cases hkj : k=j
        · subst k; exact dadd (by simp) (hi.trans (by omega))
        · simp only [ite_eq_right hkj]; exact dadd (le_of_eq (degreeOf_X_of_ne (Ne.symm hkj))) hi
      have hh:=dmul (hfactor (t^5)) (hfactor (t^6))
      split_ifs at hh ⊢ <;> simpa using hh
    _ = if j < i then 2 else 0 := by simp

theorem initialCup_spectator_filtration {n d : ℕ} (ψ : State n)
    (hd : ∀ s l, (ψ s).degreeOf l ≤ d+1)
    (hf : ∀ s l, s l=Spin.plus → (ψ s).degreeOf l ≤ d)
    (i j : Fin (n+1)) (hji : j≠i) :
    (∀ s, (initialCup ψ i s).degreeOf j≤d+1) ∧
    (∀ s, s (spectatorSlot j (pairRight i))=Spin.plus → (initialCup ψ i s).degreeOf j≤d) := by
  obtain ⟨l,rfl⟩:=Fin.exists_succAbove_eq hji
  constructor
  · intro s
    exact (degreeOf_C_mul_le _ _ _).trans (by
      rw [degreeOf_rename_of_injective Fin.succAbove_right_injective]
      exact hd _ _)
  · intro s hs
    rw [omitPair_spectatorSlot] at hs
    exact (degreeOf_C_mul_le _ _ _).trans (by
      rw [degreeOf_rename_of_injective Fin.succAbove_right_injective]
      exact hf _ _ hs)

 
theorem cupPrescription_spectator_degrees {n d : ℕ} (ψ : State n)
    (hd : ∀ s l, (ψ s).degreeOf l ≤ d+1)
    (hf : ∀ s l, s l=Spin.plus → (ψ s).degreeOf l ≤ d)
    (i j : Fin (n+1)) (hji : j≠i) (s : Fin (n+2) → Spin) :
    (cupPrescription ψ i s).degreeOf j ≤ d+3 ∧
    (s j.castSucc=Spin.plus → (cupPrescription ψ i s).degreeOf j ≤ d+2) := by
  obtain ⟨hid,hif⟩:=initialCup_spectator_filtration ψ hd hf i j hji
  have ht := transportCup_spectator_filtration i j hji (rightSpectators i) _ _ (rightSpectators_path i)
    d (initialCup ψ i) hid hif
  rw [rightSpectators_count] at ht
  simp only [spectatorSlot_last] at ht
  have hb : (C (1+T)*X i*leftFusionFactors i : MvPolynomial (Fin (n+1)) ℂ).degreeOf j ≤
      if j < i then 2 else 0 := by
    exact (dmul (dconst_mul _ (le_of_eq (degreeOf_X_of_ne hji)))
      (leftFusionFactors_spectator_degree i j hji)).trans (by omega)
  have hij : i<j ∨ j < i := lt_or_gt_of_ne (Ne.symm hji)
  constructor
  · exact (dmul hb (ht.1 s)).trans (by split_ifs <;> omega)
  · intro hs
    exact (dmul hb (ht.2 s hs)).trans (by split_ifs <;> omega)

theorem dividedCupPrescription_spectator_degree_eq {n : ℕ} (ψ : State n)
    (i j : Fin (n+1)) (hji : j≠i) (s : Fin (n+2) → Spin) :
    (dividedCupPrescription ψ i s).degreeOf j=(cupPrescription ψ i s).degreeOf j := by
  rw [cupPrescription_factor,mul_comm,degreeOf_mul_X_of_ne _ hji]

end PolynomialVacuumAlgebra

end OAI
