import OAI.Analysis.BoundedHochschild.FiniteBarCancellation

namespace OAI

/-! The bounded finite-group bar homotopy from the identity to the full
cochain average. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

variable {M G : Type*} [CStarAlgebra M] [Group G] [Fintype G]

lemma finiteGroupBarOperator_sum {I : Type*} {n : ℕ} (ρ : G →* unitary M)
    (s : Finset I) (f : I → Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (∑ i ∈ s, f i) = ∑ i ∈ s, finiteGroupBarOperator ρ (f i) :=
  map_sum (finiteGroupBarOperatorCLM ρ n) f s

lemma finiteGroupBarOperator_leftCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (leftCoboundary f) =
      f - leftCoboundary (finiteGroupBarOperator ρ f) := by
  have he : leftCoboundary (finiteGroupBarOperator ρ f) =
      ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
        leftCoboundary (finiteGroupBarInsertion ρ i f) := by
    change leftFaceLinear n (∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [he]
  change (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
    finiteGroupBarInsertion ρ i (leftCoboundary f)) = _
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, finiteGroupBarInsertion_left_zero,
    Fin.val_succ, finiteGroupBarInsertion_left_succ]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ, mul_neg, mul_one, neg_smul]

lemma finiteGroupBarOperator_rightCoboundary {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 1)) :
    finiteGroupBarOperator ρ (rightCoboundary f) =
      rightCoboundary (finiteGroupBarOperator ρ f) +
        ((-1 : ℂ) ^ (n + 1)) • finiteGroupCochainAverage ρ f := by
  have he : rightCoboundary (finiteGroupBarOperator ρ f) =
      ∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
        rightCoboundary (finiteGroupBarInsertion ρ i f) := by
    change rightFaceLinear n (∑ i : Fin (n + 1), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  rw [he]
  change (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
    finiteGroupBarInsertion ρ i (rightCoboundary f)) = _
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last, finiteGroupBarInsertion_right_castSucc,
    finiteGroupBarInsertion_right_last]

lemma finiteGroupBarOperator_middleSum {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) :
    finiteGroupBarOperator ρ (∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j) =
      -(∑ q : Fin (n + 1), ((-1 : ℂ) ^ (q.val + 1)) •
        middleCoboundary (finiteGroupBarOperator ρ f) q) := by
  have he (q : Fin (n + 1)) : middleCoboundary (finiteGroupBarOperator ρ f) q =
      ∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
        middleCoboundary (finiteGroupBarInsertion ρ i f) q := by
    change middleFaceLinear q (∑ i : Fin (n + 2), ((-1 : ℂ) ^ i.val) •
      finiteGroupBarInsertion ρ i f) = _
    rw [map_sum]
    simp only [map_smul]
    rfl
  simp_rw [he]
  rw [finiteGroupBarOperator_sum]
  simp_rw [finiteGroupBarOperator_smul]
  simp only [finiteGroupBarOperator,
    Finset.smul_sum, smul_smul, ← pow_add]
  have hleft (j : Fin (n + 2)) (i : Fin (n + 3)) : j.val + 1 + i.val = i.val + j.val + 1 := by omega
  have hright (q : Fin (n + 1)) (i : Fin (n + 2)) : q.val + 1 + i.val = i.val + q.val + 1 := by omega
  simp only [hleft, hright]
  rw [Finset.sum_comm (f := fun q : Fin (n + 1) => fun i : Fin (n + 2) =>
    ((-1 : ℂ) ^ (i.val + q.val + 1)) • middleCoboundary (finiteGroupBarInsertion ρ i f) q)]
  exact finite_bar_middle_double_sum ρ f

/-- The explicit degree-bounded finite-group operator is a cochain homotopy. -/
theorem finiteGroupBarOperator_homotopy {n : ℕ} (ρ : G →* unitary M)
    (f : Cochain M (n + 2)) :
    differential (finiteGroupBarOperator ρ f) + finiteGroupBarOperator ρ (differential f) =
      f - finiteGroupCochainAverage ρ f := by
  change (leftCoboundary (finiteGroupBarOperator ρ f) +
      (∑ q : Fin (n + 1), ((-1 : ℂ) ^ (q.val + 1)) •
        middleCoboundary (finiteGroupBarOperator ρ f) q) +
      ((-1 : ℂ) ^ (n + 2)) • rightCoboundary (finiteGroupBarOperator ρ f)) +
    finiteGroupBarOperator ρ (leftCoboundary f +
      (∑ j : Fin (n + 2), ((-1 : ℂ) ^ (j.val + 1)) • middleCoboundary f j) +
      ((-1 : ℂ) ^ (n + 3)) • rightCoboundary f) = _
  rw [finiteGroupBarOperator_add, finiteGroupBarOperator_add,
    finiteGroupBarOperator_smul, finiteGroupBarOperator_leftCoboundary,
    finiteGroupBarOperator_middleSum, finiteGroupBarOperator_rightCoboundary,
    smul_add, smul_smul]
  have hsign : (-1 : ℂ) ^ (n + 3) = -((-1 : ℂ) ^ (n + 2)) := by
    rw [show n + 3 = (n + 2) + 1 by omega, pow_succ]
    ring
  have hprod : (-1 : ℂ) ^ (n + 3) * (-1 : ℂ) ^ (n + 2) = -1 := by
    rw [hsign, neg_mul, ← mul_pow]
    norm_num
  rw [hprod, hsign, neg_smul, neg_one_smul]
  abel

end BoundedHochschild.KadisonRingrose

end

end OAI
