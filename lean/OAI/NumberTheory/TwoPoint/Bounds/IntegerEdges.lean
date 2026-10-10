import OAI.NumberTheory.TwoPoint.Bounds.WeightedRows
import OAI.NumberTheory.TwoPoint.Bounds.CenterDegree

namespace OAI

/-! Concrete centered integer edges and the padding-density cutoff. -/

namespace TwoPointCorrelations

open Finset

noncomputable def centeredTuple (P : Finset ℕ) (n : ℤ) : ℝ :=
  ∏ p ∈ P, ((if (p : ℤ) ∣ n then 1 else 0) - (p : ℝ)⁻¹)

lemma centeredTuple_add (P : Finset ℕ) (n t : ℤ)
    (ht : ∀ p ∈ P, (p : ℤ) ∣ t) : centeredTuple P (n + t) = centeredTuple P n := by
  unfold centeredTuple
  apply prod_congr rfl
  intro p hp
  simp only [dvd_add_left (ht p hp)]

lemma centeredTuple_abs (P : Finset ℕ) (n : ℤ) :
    |centeredTuple P n| =
      ∏ p ∈ P, centerMagnitude (p : ℝ)⁻¹ (decide ((p : ℤ) ∣ n)) := by
  simp [centeredTuple, abs_prod, centerMagnitude]

noncomputable def paddingDensity (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (n : ℤ) : ℝ := by
  classical
  exact (∑ q ∈ Q, if eligible q ∧ (q : ℤ) ∣ n then u q else 0) / (g n) ^ 2

noncomputable def integerEdgeKeep (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (n : ℤ) : Prop :=
  paddingDensity Q u eligible g n ≤ K / L ∧ extra n

/-- The increasing-edge coefficient, including the two endpoint cutoffs.
The auxiliary `extra` predicate carries the remaining vertex deletions. -/
noncomputable def directedIntegerEdge (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d q : ℕ) (n m : ℤ) : ℝ := by
  classical
  exact if q ∈ Q ∧ m = n + (h * q * d : ℕ) ∧ eligible q ∧ (q : ℤ) ∣ n ∧
      integerEdgeKeep Q u eligible g L K extra n ∧
      integerEdgeKeep Q u eligible g L K extra m
    then L * u q * center n / (g n * g m) else 0

noncomputable def integerEdgeMatrix {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : ι) : ℝ :=
  ∑ q ∈ Q, (directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) +
    directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i))

lemma integerEdgeMatrix_symmetric {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g center : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (h d : ℕ) (i j : ι) :
    integerEdgeMatrix site Q u eligible g center L K extra h d i j =
      integerEdgeMatrix site Q u eligible g center L K extra h d j i := by
  simp only [integerEdgeMatrix, add_comm]

lemma sum_indicator_site_le {ι : Type*} [Fintype ι]
    (site : ι → ℤ) (hinj : Function.Injective site) (n : ℤ)
    (C : ℝ) (hC : 0 ≤ C) : (∑ i, if site i = n then C else 0) ≤ C := by
  classical
  by_cases hex : ∃ i, site i = n
  · obtain ⟨i, hi⟩ := hex
    have heq (j : ι) : site j = n ↔ j = i := by
      constructor
      · intro hj
        exact hinj (hj.trans hi.symm)
      · rintro rfl
        exact hi
    simp [heq]
  · have hn (i : ι) : site i ≠ n := fun hi => hex ⟨i, hi⟩
    simpa [hn] using hC

/-- Divisibility by a padding divisor is unchanged along its integer edge. -/
lemma padding_dvd_along_edge (h q d : ℕ) (n m : ℤ)
    (hm : m = n + (h * q * d : ℕ)) : (q : ℤ) ∣ m ↔ (q : ℤ) ∣ n := by
  rw [hm]
  apply dvd_add_left
  norm_cast
  exact dvd_mul_of_dvd_left (dvd_mul_left q h) d

noncomputable def retainedPaddingAtom (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) : ℝ := by
  classical
  exact if eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n
    then L * u q / (g n) ^ 2 else 0

lemma retainedPaddingAtom_nonneg (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (q : ℕ) (hL : 0 ≤ L) (hu : 0 ≤ u q) :
    0 ≤ retainedPaddingAtom Q u eligible g L K extra n q := by
  unfold retainedPaddingAtom
  split_ifs
  · exact div_nonneg (mul_nonneg hL hu) (sq_nonneg _)
  · exact le_rfl

lemma retainedPaddingAtom_sum_le (Q : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) (g : ℤ → ℝ) (L K : ℝ)
    (extra : ℤ → Prop) (n : ℤ) (hL : 0 < L) (hK : 0 ≤ K) :
    ∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q ≤ K := by
  classical
  by_cases hk : integerEdgeKeep Q u eligible g L K extra n
  · have heq : (∑ q ∈ Q, retainedPaddingAtom Q u eligible g L K extra n q) =
        L * paddingDensity Q u eligible g n := by
      simp only [retainedPaddingAtom, paddingDensity]
      rw [← mul_div_assoc, mul_sum, sum_div]
      apply sum_congr rfl
      intro q _
      by_cases hq : eligible q ∧ (q : ℤ) ∣ n
      · simp [hq.1, hq.2, hk]
      · simp only [show ¬(eligible q ∧ (q : ℤ) ∣ n ∧ integerEdgeKeep Q u eligible g L K extra n) from
          fun hh => hq ⟨hh.1, hh.2.1⟩, hq, ite_false, mul_zero, zero_div]
    rw [heq]
    calc
      _ ≤ L * (K / L) := mul_le_mul_of_nonneg_left hk.1 hL.le
      _ = K := by field_simp
  · simpa [retainedPaddingAtom, hk] using hK

lemma centeredTuple_padding_periodic (P : Finset ℕ) (h d : ℕ)
    (hd : ∀ p ∈ P, p ∣ d) (q : ℕ) (n : ℤ) :
    centeredTuple P (n + (h * q * d : ℕ)) = centeredTuple P n := by
  apply centeredTuple_add
  intro p hp
  exact_mod_cast dvd_mul_of_dvd_right (hd p hp) (h * q)

lemma centeredTuple_abs_le_one (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (n : ℤ) :
    |centeredTuple P n| ≤ 1 := by
  rw [centeredTuple_abs]
  apply prod_le_one₀
  · intro p _
    exact centerMagnitude_nonneg _ _
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).one_lt.le
    apply centerMagnitude_le_one
    · positivity
    · exact (inv_le_one₀ (by positivity)).mpr hp1

end TwoPointCorrelations

end OAI
