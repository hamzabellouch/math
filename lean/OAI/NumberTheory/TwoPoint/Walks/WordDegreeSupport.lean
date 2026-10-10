import OAI.NumberTheory.TwoPoint.Walks.WeightedWordCoefficient

namespace OAI

/-! Endpoint degree cutoffs are already present in the exact coefficient
table. Restricting its state expansion introduces no extra deletion. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma paddingStateDeparture_degree_of_ne_zero {m : ℕ} (Qp Q : Finset ℕ)
    (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop) (L K : ℝ) (t : SignedStep)
    (S T : Finset (Fin m)) (hn : paddingStateDeparture Qp Q e eligible L K t S T ≠ 0) :
    (S.card : ℝ) ≤ 400 * Real.log L ∧ (T.card : ℝ) ≤ 400 * Real.log L := by
  unfold paddingStateDeparture at hn
  split_ifs at hn with hh
  · exact ⟨hh.2.2.2.1.2, hh.2.2.2.2.2⟩
  · contradiction

lemma all_vertices_of_endpoint_pairs {R : ℕ} (hR : 0 < R)
    (P : Fin (R + 1) → Prop) (hP : ∀ i : Fin R, P i.castSucc ∧ P i.succ) :
    ∀ i, P i := by
  cases R with
  | zero => omega
  | succ R =>
    intro i
    by_cases hi : i.val < R + 1
    · have he : (⟨i.val, hi⟩ : Fin (R + 1)).castSucc = i := Fin.ext rfl
      simpa only [he] using (hP ⟨i.val, hi⟩).1
    · have he : (Fin.last R).succ = i := Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
      simpa only [he] using (hP (Fin.last R)).2

lemma actualWordCoefficient_degree_of_ne_zero {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J))
    (hR : 0 < R) (hn : actualWordCoefficient Qp Q e eligible L K step p S bits ≠ 0) :
    ∀ i, ((S i).card : ℝ) ≤ 400 * Real.log L := by
  have hprod : (∏ i : Fin R, paddingStateDeparture Qp Q e eligible L K (step i)
      (S i.castSucc) (S i.succ)) ≠ 0 := (mul_ne_zero_iff.mp hn).1
  apply all_vertices_of_endpoint_pairs hR
  intro i
  apply paddingStateDeparture_degree_of_ne_zero Qp Q e eligible L K (step i)
  exact (prod_ne_zero_iff.mp hprod) i (mem_univ i)

lemma actualWordCoefficient_truncation {R J m : ℕ}
    (Qp Q : Finset ℕ) (e : Fin m ≃ Qp) (eligible : SignedStep → ℕ → Prop)
    (L K : ℝ) (step : Fin R → SignedStep) (p : Fin R → Fin J → ℕ)
    (S : Fin (R + 1) → Finset (Fin m)) (bits : BooleanCube (R * J))
    (hR : 0 < R) (hL : 1 ≤ L) :
    (if ∀ i, (S i).card ≤ ⌊400 * Real.log L⌋₊
      then actualWordCoefficient Qp Q e eligible L K step p S bits else 0) =
      actualWordCoefficient Qp Q e eligible L K step p S bits := by
  by_cases hn : actualWordCoefficient Qp Q e eligible L K step p S bits = 0
  · simp [hn]
  · have hcard := actualWordCoefficient_degree_of_ne_zero Qp Q e eligible L K step p S bits hR hn
    have hm : ∀ i, (S i).card ≤ ⌊400 * Real.log L⌋₊ := fun i =>
      (Nat.le_floor_iff (mul_nonneg (by norm_num) (Real.log_nonneg hL))).mpr (hcard i)
    exact ite_eq_left hm

end TwoPointCorrelations

end OAI
