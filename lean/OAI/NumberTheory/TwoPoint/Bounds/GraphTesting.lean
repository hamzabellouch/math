import OAI.NumberTheory.TwoPoint.Bounds.PrimeFamilyGraph
import OAI.NumberTheory.TwoPoint.Bounds.PositiveRowMajorant
import OAI.NumberTheory.TwoPoint.Bounds.WeightedMatrixTest

namespace OAI

/-! The deterministic quadratic-form estimate on every block, including
exceptional blocks. The projected support pays only a power of the mass. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma matrixOperator_sum {D V : Type*} [Fintype D] [Fintype V] [DecidableEq V]
    (A : D → V → V → ℂ) :
    matrixOperator (fun i j => ∑ d, A d i j) = ∑ d, matrixOperator (A d) := by
  ext v i
  simp only [_root_.sum_apply, matrixOperator_apply,
    WithLp.ofLp_sum, Finset.sum_apply, sum_mul]
  rw [sum_comm]

lemma sum_familyCenter_abs_le {J : ℕ} (P : Fin J → Finset ℕ)
    (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l)) (n : ℤ) (W : ℝ)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (hdegree : (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J) :
    (∑ d : (j : Fin J) → P j,
      |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d n|) ≤ (8 * W) ^ J := by
  have hb := abs_centeredTuple_sum_le P hprime hdisjoint n W hV hdegree
  rw [primeTupleDivisors, sum_image] at hb
  · simpa only [familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
      _ (selectedPrimeValues_injective _ hdisjoint), familyTuple] using hb
  · intro d _ e _ hde
    exact primeTuple_injective hprime hdisjoint hde

theorem prime_graph_test_deterministic {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (hinj : Function.Injective site)
    (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop)
    (hL : 0 < L) (hK : 0 ≤ K) (hW : 0 ≤ W)
    (hu : ∀ q ∈ Q, 0 ≤ u q) (hg : ∀ n, 0 < g n)
    (hV : ∀ j, primeHarmonicMass (P j) ≤ 2 * W)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, ‖v i‖ ≤ g (site i))
    (hdegree : ∀ i, v i ≠ 0 →
      (actualPaddingDegree (univ.biUnion P) (site i) : ℝ) ≤ 6 * W * J)
    (G : ℝ) (hG : 0 ≤ G) (hweight : ∀ i, v i ≠ 0 → (g (site i)) ^ 2 ≤ G) :
    ‖inner ℂ v ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate d) v)‖ ≤
        Fintype.card V * (2 * K * (8 * W) ^ J) * G := by
  let A (d : (j : Fin J) → P j) := maskedIntegerEdgeMatrix site Q u
    (eligible (familyTuple (fun j (p : P j) => p.val) d)) g
    (familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d)
    L K (extra (familyTuple (fun j (p : P j) => p.val) d)) h
    (familyTuple (fun j (p : P j) => p.val) d)
    (gate (familyTuple (fun j (p : P j) => p.val) d))
  have hrow (i : V) (hi : v i ≠ 0) :
      (∑ j, ‖∑ d, A d i j‖ * g (site j) / g (site i)) ≤ 2 * K * (8 * W) ^ J := by
    calc
      _ ≤ ∑ j, (∑ d, ‖A d i j‖) * g (site j) / g (site i) := by
        apply sum_le_sum
        intro j _
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hg _).le) (hg _).le
      _ = ∑ d, ∑ j, ‖A d i j‖ * g (site j) / g (site i) := by
        simp only [sum_mul, sum_div]
        rw [sum_comm]
      _ ≤ ∑ d : (j : Fin J) → P j,
          2 * K * |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by
        apply sum_le_sum
        intro d _
        exact maskedIntegerEdgeMatrix_weighted_row site hinj Q u _ g _ L K _ h _ _
          hL hK hu hg (fun q _ n => familyCenter_padding_periodic _ _ d h q n) i
      _ = 2 * K * ∑ d : (j : Fin J) → P j,
          |familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d (site i)| := by rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (sum_familyCenter_abs_le P hprime hdisjoint (site i) W hV (hdegree i hi)) (by positivity)
  have ht := weighted_matrix_test_uniform (fun i j => ∑ d, A d i j)
    (fun i => g (site i)) (2 * K * (8 * W) ^ J) G
    (fun i => hg _) (by positivity) hG v hv hrow hweight
  rw [matrixOperator_sum] at ht
  exact ht

end TwoPointCorrelations

end OAI
