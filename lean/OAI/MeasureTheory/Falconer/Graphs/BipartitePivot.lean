import OAI.MeasureTheory.Falconer.Estimates.FinitePopularity

namespace OAI

/-! The dense-neighborhood pivot used in the scalar additive-energy
argument. Integer vertices are sufficient for the quantized sumsets. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def integerNeighbors (B : Finset ℤ) (e : ℤ → ℤ → Prop) (a : ℤ) : Finset ℤ :=
  B.filter fun b => e a b

noncomputable def integerCommonNeighbors (A : Finset ℤ) (e : ℤ → ℤ → Prop)
    (b c : ℤ) : Finset ℤ := A.filter fun a => e a b ∧ e a c

noncomputable def integerBadPairs (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) :
    Finset (ℤ × ℤ) := (B ×ˢ B).filter fun p => ((integerCommonNeighbors A e p.1 p.2).card : ℝ) < L

noncomputable def integerBadPairsAt (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (L : ℝ) (a : ℤ) : Finset (ℤ × ℤ) :=
  (integerBadPairs A B e L).filter fun p => e a p.1 ∧ e a p.2

theorem integer_bad_pairs_sum (A B : Finset ℤ) (e : ℤ → ℤ → Prop) (L : ℝ) :
    (∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) =
      ∑ p ∈ integerBadPairs A B e L, ((integerCommonNeighbors A e p.1 p.2).card : ℝ) := by
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := A) (t := integerBadPairs A B e L) (fun a p => e a p.1 ∧ e a p.2)
  exact_mod_cast he

theorem integer_bad_pairs_sum_le (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    {L : ℝ} (hL : 0 ≤ L) :
    (∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) ≤ L*(B.card : ℝ)^2 := by
  rw [integer_bad_pairs_sum]
  calc
    _ ≤ ∑ _p ∈ integerBadPairs A B e L, L := Finset.sum_le_sum fun p hp =>
      ((Finset.mem_filter.mp hp).2).le
    _ = L*((integerBadPairs A B e L).card : ℝ) := by simp [mul_comm]
    _ ≤ L*(B.card : ℝ)^2 := by
      apply mul_le_mul_of_nonneg_left _ hL
      have hc := Finset.card_le_card (show integerBadPairs A B e L ⊆ B ×ˢ B from Finset.filter_subset _ _)
      simpa only [Finset.card_product,Nat.cast_mul,pow_two] using (Nat.cast_le (α := ℝ)).mpr hc

theorem integer_dense_pivot (A B : Finset ℤ) (e : ℤ → ℤ → Prop)
    (hA : A.Nonempty) (hB : B.Nonempty) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 ≤ L)
    (hsmall : L ≤ ρ^2*(A.card : ℝ)/32)
    (hdense : ρ*(A.card : ℝ)*(B.card : ℝ) ≤
      ∑ a ∈ A, ((integerNeighbors B e a).card : ℝ)) :
    ∃ a ∈ A, ρ*(B.card : ℝ)/2 ≤ ((integerNeighbors B e a).card : ℝ) ∧
      16*((integerBadPairsAt A B e L a).card : ℝ) ≤
        ρ*(B.card : ℝ)*((integerNeighbors B e a).card : ℝ) := by
  have ha : 0 < (A.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hb : 0 < (B.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  let c : ℝ := 16/(ρ*(B.card : ℝ))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbad := integer_bad_pairs_sum_le A B e hL
  have hloss : c*(∑ a ∈ A, ((integerBadPairsAt A B e L a).card : ℝ)) ≤
      ρ*(A.card : ℝ)*(B.card : ℝ)/2 := by
    calc
      _ ≤ c*(L*(B.card : ℝ)^2) := mul_le_mul_of_nonneg_left hbad hc
      _ ≤ c*((ρ^2*(A.card : ℝ)/32)*(B.card : ℝ)^2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)) hc
      _ = _ := by dsimp [c]; field_simp; ring
  let score := fun a => ((integerNeighbors B e a).card : ℝ)-c*((integerBadPairsAt A B e L a).card : ℝ)
  have htotal : ∑ _a ∈ A, ρ*(B.card : ℝ)/2 ≤ ∑ a ∈ A, score a := by
    simp only [score,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
    linarith
  obtain ⟨a,haA,hascore⟩ := Finset.exists_le_of_sum_le hA htotal
  have hscore : ρ*(B.card : ℝ)/2 ≤
      ((integerNeighbors B e a).card : ℝ)-c*((integerBadPairsAt A B e L a).card : ℝ) := hascore
  have hnonneg : 0 ≤ c*((integerBadPairsAt A B e L a).card : ℝ) := mul_nonneg hc (Nat.cast_nonneg _)
  refine ⟨a,haA,by linarith,?_⟩
  have hmul := mul_le_mul_of_nonneg_left hscore (show 0 ≤ ρ*(B.card : ℝ) by positivity)
  have he : ρ*(B.card : ℝ)*(c*((integerBadPairsAt A B e L a).card : ℝ)) =
      16*((integerBadPairsAt A B e L a).card : ℝ) := by
    dsimp [c]
    field_simp
  nlinarith

end Falconer

end OAI
