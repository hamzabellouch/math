import OAI.NumberTheory.TwoPoint.Walks.RetainedComplexMatrix
import OAI.NumberTheory.TwoPoint.Bounds.PrimeLiouvilleQuadratic
import OAI.NumberTheory.TwoPoint.Bounds.ProjectedLiouvilleVector

namespace OAI

/-! The canonical tuple graph has the same retained real kernel for all bounded tests. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def retainedPrimeMatrix {J : ℕ} {V : Type*} [Fintype V]
    (P : Fin J → Finset ℕ) (site : V → ℤ) (Q : Finset ℕ)
    (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop) (g : ℤ → ℝ)
    (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) : Matrix V V ℂ :=
  ∑ d : (j : Fin J) → P j, retainedDirectedMatrix site Q u
    (eligible (∏ j, (d j).val)) g (centeredTuple (∏ j, (d j).val).primeFactors)
    L K (extra (∏ j, (d j).val)) keep h (∏ j, (d j).val) (gate (∏ j, (d j).val))

theorem prime_graph_retained_bilinear {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (g : ℤ → ℝ) (L K : ℝ) (extra : ℕ → ℤ → Prop) (keep : ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (hg : ∀ z, g z ≠ 0) (F G : ℤ → ℂ) :
    let vf := WithLp.toLp 2 (fun i => retainedComplexScalar g keep (fun z => star (F z)) (site i))
    let vg := WithLp.toLp 2 (fun i => retainedComplexScalar g keep G (site i))
    let A := retainedPrimeMatrix P site Q u eligible g L K extra keep h gate
    inner ℂ vf ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
      (fun _ _ => 0) site Q u eligible g L K extra h gate d) vg) =
        ∑ i, ∑ j, F (site i) * G (site j) * (A i j + A j i) := by
  dsimp only
  let vf : EuclideanSpace ℂ V := WithLp.toLp 2
    (fun i => retainedComplexScalar g keep (fun z => star (F z)) (site i))
  let vg : EuclideanSpace ℂ V := WithLp.toLp 2
    (fun i => retainedComplexScalar g keep G (site i))
  have hd (d : (j : Fin J) → P j) :
      inner ℂ vf (primeFamilyGraphOperator (fun j (p : P j) => p.val)
        (fun _ _ => 0) site Q u eligible g L K extra h gate d vg) =
        ∑ i, ∑ j, F (site i) * G (site j) *
          (retainedDirectedMatrix site Q u (eligible (∏ j, (d j).val)) g
            (centeredTuple (∏ j, (d j).val).primeFactors) L K
            (extra (∏ j, (d j).val)) keep h (∏ j, (d j).val) (gate (∏ j, (d j).val)) i j +
          retainedDirectedMatrix site Q u (eligible (∏ j, (d j).val)) g
            (centeredTuple (∏ j, (d j).val).primeFactors) L K
            (extra (∏ j, (d j).val)) keep h (∏ j, (d j).val) (gate (∏ j, (d j).val)) j i) := by
    have hc : familyCenter (fun j (p : P j) => p.val) (fun _ _ => 0) d =
        centeredTuple (∏ j, (d j).val).primeFactors := by
      funext n
      exact familyCenter_zero_eq_centeredTuple _ (fun j p => hprime j _ p.property)
        d (selectedPrimeValues_injective d hdisjoint) n
    unfold primeFamilyGraphOperator
    rw [hc]
    exact retained_matrix_bilinear site Q u _ g _ L K _ keep h _ _ (hgate _) hg F G
  change inner ℂ vf ((∑ d, primeFamilyGraphOperator (fun j (p : P j) => p.val)
    (fun _ _ => 0) site Q u eligible g L K extra h gate d) vg) = _
  rw [_root_.sum_apply, inner_sum]
  simp_rw [hd]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simp only [retainedPrimeMatrix, Matrix.sum_apply, ← mul_sum, ← sum_add_distrib]

lemma projectedComplexVector_eq {V : Type*} [Fintype V] [DecidableEq V]
    (Q : Finset ℕ) (L : ℝ) (site : V → ℤ) (keep : ℤ → Prop) (F : ℤ → ℂ) :
    coordinateProjection (fun i => keep (site i)) (paddingTestVector Q L site F) =
      WithLp.toLp 2 (fun i => retainedComplexScalar (actualPaddingVertex Q)
        (fun n => keep n ∧ actualPaddingDegreeCut Q L n) F (site i)) := by
  ext i
  by_cases hp : keep (site i) <;> by_cases hq : actualPaddingDegreeCut Q L (site i) <;>
    simp [coordinateProjection_apply, paddingTestVector, retainedComplexScalar, hp, hq]

theorem projected_prime_complex_bilinear {J : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (P : Fin J → Finset ℕ) (hprime : ∀ j, ∀ p ∈ P j, p.Prime)
    (hdisjoint : ∀ j l, l ≠ j → Disjoint (P j) (P l))
    (site : V → ℤ) (Q Qp : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → ℕ → Prop)
    (L K W : ℝ) (extra : ℕ → ℤ → Prop) (h : ℕ)
    (gate : ℕ → V → V → Prop) (hgate : ∀ d i j, gate d i j ↔ gate d j i)
    (F G : ℤ → ℂ) :
    let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
      site Q u eligible (actualPaddingVertex Qp) L K extra h gate
    let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
    let proj := coordinateProjection (fun i => keep (site i))
    let vf := paddingTestVector Qp L site (fun n => star (F n))
    let vg := paddingTestVector Qp L site G
    let A := retainedPrimeMatrix P site Q u eligible (actualPaddingVertex Qp) L K extra
      (fun n => keep n ∧ actualPaddingDegreeCut Qp L n) h gate
    inner ℂ vf ((proj * (∑ d, B d) * proj) vg) =
      ∑ i, ∑ j, F (site i) * G (site j) * (A i j + A j i) := by
  dsimp only
  let keep := fun n => (actualPaddingDegree (univ.biUnion P) n : ℝ) ≤ 6 * W * J
  let proj := coordinateProjection (fun i => keep (site i))
  let B := primeFamilyGraphOperator (fun j (p : P j) => p.val) (fun _ _ => 0)
    site Q u eligible (actualPaddingVertex Qp) L K extra h gate
  let vf := paddingTestVector Qp L site (fun n => star (F n))
  let vg := paddingTestVector Qp L site G
  have he := (coordinateProjection_selfAdjoint (fun i => keep (site i))).isSymmetric
    vf ((∑ d, B d) (proj vg))
  have hmain := prime_graph_retained_bilinear P hprime hdisjoint site Q u eligible
    (actualPaddingVertex Qp) L K extra (fun n => keep n ∧ actualPaddingDegreeCut Qp L n)
    h gate hgate (actualPaddingVertex_ne_zero Qp) F G
  rw [← projectedComplexVector_eq, ← projectedComplexVector_eq] at hmain
  exact he.symm.trans hmain

end TwoPointCorrelations

end OAI
