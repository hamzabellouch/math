import OAI.Combinatorics.Progressions.Estimates.BoundedQuotientFunctional
import OAI.Combinatorics.Progressions.Geometry.EmbeddingCoordinateHeight

namespace OAI

section

namespace Erdos3

open Module

theorem exists_quotient_functional_with_bounded_denominator
    {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]
    (U I : Submodule ℚ V) (b : Basis ι ℚ (V ⧸ I))
    (v : κ → V) (hspan : Submodule.span ℚ (Set.range v) = U)
    (η : V →ₗ[ℚ] ℚ) (hann : U ⊓ I ≤ η.ker)
    {H K : ℕ} (hH : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (b.repr (I.mkQ (v i)) j) H)
    (hη : ∀ i, RationalHeightLE (η (v i)) K)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) :
    ∃ (ξ : (V ⧸ I) →ₗ[ℚ] ℚ) (l : ℕ),
      (∀ x ∈ U, ξ (I.mkQ x) = η x) ∧
      (∀ i, rationalLogHeight (ξ (b i)) ≤ (p + 2) ^ 8) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      ∀ i, ∃ z : ℤ, (l : ℚ) * ξ (b i) = z := by
  classical
  let _ : FiniteDimensional ℚ (V ⧸ I) := b.finiteDimensional_of_finite
  let m := finrank ℚ (U.map I.mkQ)
  have hm : (m : ℝ) ≤ p := by
    apply le_trans _ hd
    exact_mod_cast (Submodule.finrank_le (U.map I.mkQ)).trans_eq (finrank_eq_card_basis b)
  let C := (m + 1) * (rationalSolveHeight m H * K) ^ m
  have hC : (C : ℝ) ≤ Real.exp ((p + 2) ^ 8) :=
    embedding_coordinate_height_budget m m H K hp hm hm hHp hKp
  obtain ⟨ξ, hξ, hheight⟩ := exists_bounded_quotient_functional U I b v hspan η hann hH hv hη
  let l := arrayDenominator (fun i => ξ (b i))
  have hl : l ≤ C ^ Fintype.card ι :=
    arrayDenominator_le _ (fun i => (hheight i).2)
  have hlp : (l : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    calc
      _ ≤ (C : ℝ) ^ Fintype.card ι := by exact_mod_cast hl
      _ ≤ Real.exp ((p + 2) ^ 8) ^ Fintype.card ι :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hC _
      _ = Real.exp ((Fintype.card ι : ℝ) * (p + 2) ^ 8) :=
        (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + 2) * (p + 2) ^ 8) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hd.trans (by linarith)) (by positivity))
      _ = _ := by congr 1; ring
  exact ⟨ξ, l, hξ, fun i => rationalLogHeight_le_of_height (hheight i) hC,
    arrayDenominator_pos _, hlp,
    fun i => ⟨clearedArray (fun j => ξ (b j)) i, (clearedArray_cast _ i).symm⟩⟩

end Erdos3

end

end OAI
