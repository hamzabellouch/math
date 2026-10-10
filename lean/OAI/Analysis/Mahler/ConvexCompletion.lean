import OAI.Analysis.Mahler.ConvexTransfer

namespace OAI

namespace SymmetricMahler
open Set Finset MeasureTheory Filter
open scoped Topology
variable {I J J' : Type*} [Fintype I] [fintypeJ : Fintype J] [fintypeJPrime : Fintype J'] [decidableEqI : DecidableEq I]

omit fintypeJ decidableEqI in
lemma convex_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : Convex ℝ (stripBody A) := by
  intro x hx y hy a b ha hb hab j
  have he : measurement A (a • x + b • y) j =
      a * measurement A x j + b * measurement A y j := by
    simp only [measurement, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      sum_add_distrib, mul_sum]
    apply congrArg₂ (· + ·) <;> apply sum_congr rfl <;> intros <;> ring
  rw [he]
  calc
    |a * measurement A x j + b * measurement A y j| ≤
        |a * measurement A x j| + |b * measurement A y j| := abs_add_le _ _
    _ = a * |measurement A x j| + b * |measurement A y j| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left (hx j) ha) (mul_le_mul_of_nonneg_left (hy j) hb)
    _ = 1 := by linarith

omit fintypeJ decidableEqI in
lemma symmetric_stripBody [Fintype J] [DecidableEq I] (A : J → I → ℝ) : ∀ x ∈ stripBody A, -x ∈ stripBody A := by
  intro x hx j
  simpa [measurement, mul_neg, sum_neg_distrib] using hx j

omit fintypeJ fintypeJPrime decidableEqI in
lemma stripBody_reindex [Fintype J] [Fintype J'] [DecidableEq I] (A : J → I → ℝ) (e : J' ≃ J) :
    stripBody (fun j => A (e j)) = stripBody A := by
  ext x
  constructor
  · intro hx j
    simpa only [measurement, e.apply_symm_apply] using hx (e.symm j)
  · intro hx j
    exact hx (e j)

omit fintypeJ fintypeJPrime decidableEqI in
lemma measurement_reindex_injective [Fintype J] [Fintype J'] [DecidableEq I] (A : J → I → ℝ) (e : J' ≃ J)
    (hA : Function.Injective (measurement A)) :
    Function.Injective (measurement (fun j => A (e j))) := by
  intro x y h
  apply hA
  funext j
  simpa only [measurement, e.apply_symm_apply] using congrFun h (e.symm j)

/-- The arbitrary-body bound follows from finite-matrix bounds indexed by Fin N rows. -/
theorem arbitrary_body_bound_of_fin_matrices {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K)
    (hint : (interior K).Nonempty) (C : ℝ)
    (hfinite : ∀ N (A : Fin N → Fin n → ℝ), Function.Injective (measurement A) →
      C ≤ (volume (stripBody A)).toReal * (volume (coordinatePolar (stripBody A))).toReal) :
    C ≤ (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  apply arbitrary_body_bound_of_finite_strips hK hconv hsym hint C
  intro N A hA
  let e := (Fintype.equivFin (Fin n ⊕ Fin N)).symm
  have h := hfinite _ (fun j => A (e j)) (measurement_reindex_injective A e hA)
  rwa [stripBody_reindex] at h

theorem symmetric_mahler_of_finite_strips {n : ℕ} (_hn : 1 ≤ n)
    (hfinite : ∀ N (A : Fin N → Fin n → ℝ), Function.Injective (measurement A) →
      (4 : ℝ)^n / (Nat.factorial n : ℝ) ≤
        (volume (stripBody A)).toReal * (volume (coordinatePolar (stripBody A))).toReal)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    (4 : ℝ)^n / (Nat.factorial n : ℝ) ≤
      (volume K).toReal * (volume (coordinatePolar K)).toReal :=
  arbitrary_body_bound_of_fin_matrices hK hconv hsym hint _ hfinite

end SymmetricMahler

end OAI
