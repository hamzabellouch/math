import OAI.Analysis.BoundedHochschild.AveragedBarFaces

namespace OAI

/-! Finite signed cancellation of the averaged bar-insertion faces. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

private def faceShuffle (n : ℕ) :
    (Fin (n + 2) × Fin (n + 1)) ≃ (Fin (n + 2) × Fin (n + 1)) where
  toFun p := (p.1.succAbove p.2, p.2.predAbove p.1)
  invFun p := (p.1.succAbove p.2, p.2.predAbove p.1)
  left_inv p := by
    exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
      (Fin.predAbove_predAbove_succAbove p.1 p.2)
  right_inv p := by
    exact Prod.ext (Fin.succAbove_succAbove_predAbove p.1 p.2)
      (Fin.predAbove_predAbove_succAbove p.1 p.2)

private lemma sum_faceShuffle {n : ℕ} (F : Fin (n + 2) → Fin (n + 1) → Cochain M (n + 2)) :
    (∑ j : Fin (n + 2), ∑ k : Fin (n + 1), F (j.succAbove k) (k.predAbove j)) =
      ∑ i : Fin (n + 2), ∑ q : Fin (n + 1), F i q := by
  simpa only [Fintype.sum_prod_type] using
    Fintype.sum_equiv (faceShuffle n)
      (fun p => F (p.1.succAbove p.2) (p.2.predAbove p.1))
      (fun p => F p.1 p.2) (fun _ => rfl)

private lemma bar_middle_adjacent (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) :
    ((-1 : ℂ) ^ (j.val + j.val + 1)) •
        finiteGroupBarInsertion ρ j.castSucc (middleCoboundary f j) +
      ((-1 : ℂ) ^ (j.val + 1 + j.val + 1)) •
        finiteGroupBarInsertion ρ j.succ (middleCoboundary f j) = 0 := by
  rw [finiteGroupBarInsertion_middle_castSucc, finiteGroupBarInsertion_middle_succ]
  have h : j.val + 1 + j.val + 1 = (j.val + j.val + 1) + 1 := by omega
  have hp : (-1 : ℂ) ^ (j.val + 1 + j.val + 1) =
      -((-1 : ℂ) ^ (j.val + j.val + 1)) := by
    rw [h, pow_succ]
    ring
  rw [hp, neg_smul, add_neg_cancel]

private lemma bar_middle_off_face (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
        (middleCoboundary f j) =
      middleCoboundary (finiteGroupBarInsertion ρ (j.succAbove k) f) (k.predAbove j) := by
  by_cases hkj : k.castSucc < j
  · have hj0 : j ≠ 0 := by
      intro hj
      subst j
      exact (not_lt_zero hkj)
    let q : Fin (n + 1) := j.pred hj0
    have hq : q.succ = j := Fin.succ_pred _ _
    have hi : j.succAbove k = k.castSucc := Fin.succAbove_of_castSucc_lt _ _ hkj
    have hp : k.predAbove j = q := Fin.predAbove_of_castSucc_lt _ _ hkj
    have ht : j.castSucc.succAbove (j.succAbove k) = k.castSucc.castSucc := by
      rw [hi, Fin.succAbove_of_castSucc_lt]
      exact hkj
    rw [ht, hi, hp, ← hq]
    exact finiteGroupBarInsertion_middle_after ρ f k.castSucc q (by
      have hv : k.val < j.val := hkj
      dsimp [q]
      omega)
  · have hjk : j.val ≤ k.val := le_of_not_gt hkj
    have hjlast : j ≠ Fin.last (n + 1) := by
      intro hj
      subst j
      have hk := k.isLt
      simp only [Fin.val_last] at hjk
      omega
    let q : Fin (n + 1) := j.castPred hjlast
    have hq : q.castSucc = j := Fin.castSucc_castPred _ _
    have hi : j.succAbove k = k.succ := Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hkj)
    have hp : k.predAbove j = q := Fin.predAbove_of_le_castSucc _ _ (le_of_not_gt hkj)
    have ht : j.castSucc.succAbove (j.succAbove k) = k.succ.succ := by
      rw [hi, Fin.succAbove_of_le_castSucc]
      simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
      omega
    rw [ht, hi, hp, ← hq]
    exact finiteGroupBarInsertion_middle_before ρ f k.succ q (by
      dsimp [q]
      omega)

private lemma bar_middle_row (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) :
    (∑ i : Fin (n + 3), ((-1 : ℂ) ^ (i.val + j.val + 1)) •
      finiteGroupBarInsertion ρ i (middleCoboundary f j)) =
    ∑ k : Fin (n + 1),
      ((-1 : ℂ) ^ ((j.castSucc.succAbove (j.succAbove k)).val + j.val + 1)) •
        finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
          (middleCoboundary f j) := by
  rw [Fin.sum_univ_succAbove _ j.castSucc, Fin.sum_univ_succAbove _ j]
  simp only [Fin.succAbove_castSucc_self, Fin.val_castSucc, Fin.val_succ]
  rw [← add_assoc, bar_middle_adjacent, zero_add]

private lemma bar_middle_off_parity {n : ℕ} (j : Fin (n + 2)) (k : Fin (n + 1)) :
    (j.castSucc.succAbove (j.succAbove k)).val + j.val + 1 =
      (j.succAbove k).val + (k.predAbove j).val + 2 := by
  by_cases hkj : k.castSucc < j
  · rw [Fin.succAbove_of_castSucc_lt j k hkj,
      Fin.predAbove_of_castSucc_lt k j hkj,
      Fin.succAbove_of_castSucc_lt j.castSucc k.castSucc hkj]
    change k.val + j.val + 1 = k.val + (j.val - 1) + 2
    have hv : k.val < j.val := hkj
    omega
  · have hjk := le_of_not_gt hkj
    rw [Fin.succAbove_of_le_castSucc j k hjk,
      Fin.predAbove_of_le_castSucc k j hjk,
      Fin.succAbove_of_le_castSucc j.castSucc k.succ (by
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] at *
        omega)]
    change (k.val + 1 + 1) + j.val + 1 = (k.val + 1) + j.val + 2
    omega

private lemma bar_middle_off_signed (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) (j : Fin (n + 2)) (k : Fin (n + 1)) :
    ((-1 : ℂ) ^ ((j.castSucc.succAbove (j.succAbove k)).val + j.val + 1)) •
        finiteGroupBarInsertion ρ (j.castSucc.succAbove (j.succAbove k))
          (middleCoboundary f j) =
    -(((-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 1)) •
        middleCoboundary (finiteGroupBarInsertion ρ (j.succAbove k) f) (k.predAbove j)) := by
  rw [bar_middle_off_face, bar_middle_off_parity]
  have hp : (-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 2) =
      -((-1 : ℂ) ^ ((j.succAbove k).val + (k.predAbove j).val + 1)) := by
    rw [show (j.succAbove k).val + (k.predAbove j).val + 2 =
      ((j.succAbove k).val + (k.predAbove j).val + 1) + 1 by omega, pow_succ]
    ring
  rw [hp, neg_smul]

lemma finite_bar_middle_double_sum (ρ : G →* unitary M) {n : ℕ}
    (f : Cochain M (n + 2)) :
    (∑ j : Fin (n + 2), ∑ i : Fin (n + 3),
      ((-1 : ℂ) ^ (i.val + j.val + 1)) • finiteGroupBarInsertion ρ i (middleCoboundary f j)) =
    -(∑ i : Fin (n + 2), ∑ q : Fin (n + 1),
      ((-1 : ℂ) ^ (i.val + q.val + 1)) •
        middleCoboundary (finiteGroupBarInsertion ρ i f) q) := by
  simp_rw [bar_middle_row, bar_middle_off_signed]
  simp only [Finset.sum_neg_distrib]
  congr 1
  exact sum_faceShuffle (fun i q => ((-1 : ℂ) ^ (i.val + q.val + 1)) •
    middleCoboundary (finiteGroupBarInsertion ρ i f) q)

end BoundedHochschild.KadisonRingrose

end

end OAI
