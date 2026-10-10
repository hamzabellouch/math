import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialScalar

namespace OAI

/-! Finite polynomial families can be padded to a common degree and added
without changing their values or their smooth-coefficient property. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma eval_sumFinset {ι : Type*} (s : Finset ι) (e : ι → Expression)
    (G : Base → Space) (z : Base × ℝ) :
    (sumFinset s e).eval G z = ∑ i ∈ s, (e i).eval G z := by
  classical
  rw [sumFinset,eval_sumList,← List.sum_toFinset _ s.nodup_toList,
    Finset.toList_toFinset]

end Expression

namespace Perturbation

private lemma sum_fin_zero_extension {α : Type*} [AddCommMonoid α]
    {n N : ℕ} (hnN : n ≤ N) (f : Fin n → α) :
    (∑ r : Fin N, if h : r.val < n then f ⟨r.val,h⟩ else 0) = ∑ r : Fin n, f r := by
  classical
  let g : ℕ → α := fun r => if h : r < n then f ⟨r,h⟩ else 0
  calc
    (∑ r : Fin N, if h : r.val < n then f ⟨r.val,h⟩ else 0) =
        ∑ r ∈ Finset.range N, g r := Fin.sum_univ_eq_sum_range g N
    _ = ∑ r ∈ Finset.range n, g r := by
      symm
      apply Finset.sum_subset (Finset.range_mono hnN)
      intro r _ hr
      have hn : ¬ r < n := fun h => hr (Finset.mem_range.mpr h)
      simp only [g,dite_eq_right hn]
    _ = ∑ r : Fin n, f r := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      change (if h : r.val < n then f ⟨r.val,h⟩ else 0) = f r
      rw [dite_eq_left r.isLt]

/-- Higher unused powers have the actual zero expression as coefficient. -/
def padTensorPolynomial {n N : ℕ} (P : Fin 3 → Fin n → Expression) :
    Fin 3 → Fin N → Expression :=
  fun k r => if h : r.val < n then P k ⟨r.val,h⟩ else .coeff (fun _ => 0)

lemma padTensorPolynomial_smooth {n N : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ) (k : Fin 3) (r : Fin N) :
    (padTensorPolynomial P k r).SmoothCoeffs univ := by
  unfold padTensorPolynomial
  split
  · exact hP _ _
  · exact contDiffOn_const

lemma padTensorPolynomial_value {n N : ℕ} (P : Fin 3 → Fin n → Expression)
    (hnN : n ≤ N) (ε : ℝ) (G : Base → Space) (t : ℝ) :
    coordinatePolynomialValue (padTensorPolynomial (N := N) P) ε G t =
      coordinatePolynomialValue P ε G t := by
  classical
  funext p k
  change (∑ r : Fin N, ε ^ (r.val+1) * (padTensorPolynomial P k r).eval G
      (planeCoordinateIsometry.symm p,t)) =
    ∑ r : Fin n, ε ^ (r.val+1) * (P k r).eval G (planeCoordinateIsometry.symm p,t)
  calc
    _ = ∑ r : Fin N, if h : r.val < n then
        ε ^ (r.val+1) * (P k ⟨r.val,h⟩).eval G (planeCoordinateIsometry.symm p,t)
        else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r.val < n
      · simp only [padTensorPolynomial,dite_eq_left hr]
      · simp only [padTensorPolynomial,dite_eq_right hr,Expression.eval,mul_zero]
    _ = _ := sum_fin_zero_extension hnN
      (fun r => ε ^ (r.val+1) * (P k r).eval G (planeCoordinateIsometry.symm p,t))

/-- The largest number of powers in a finite dependent family. -/
def polynomialFamilyDegree {ι : Type*} [Fintype ι] (n : ι → ℕ) : ℕ :=
  Finset.univ.sup n

lemma le_polynomialFamilyDegree {ι : Type*} [Fintype ι] (n : ι → ℕ) (i : ι) :
    n i ≤ polynomialFamilyDegree n :=
  Finset.le_sup (f := n) (Finset.mem_univ i)

/-- Add the coefficient expressions after padding every member to the
same degree. No map or perturbation parameter enters this construction. -/
def sumTensorPolynomials {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (P : (i : ι) → Fin 3 → Fin (n i) → Expression) :
    Fin 3 → Fin (polynomialFamilyDegree n) → Expression :=
  fun k r => Expression.sumFinset Finset.univ (fun i => padTensorPolynomial (P i) k r)

lemma sumTensorPolynomials_smooth {ι : Type*} [Fintype ι] {n : ι → ℕ}
    {P : (i : ι) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k r, (P i k r).SmoothCoeffs univ) (k : Fin 3)
    (r : Fin (polynomialFamilyDegree n)) :
    (sumTensorPolynomials P k r).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact padTensorPolynomial_smooth (hP i) k r

lemma sumTensorPolynomials_value {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (P : (i : ι) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : Base → Space) (t : ℝ) :
    coordinatePolynomialValue (sumTensorPolynomials P) ε G t =
      ∑ i, coordinatePolynomialValue (P i) ε G t := by
  classical
  funext p k
  simp only [Finset.sum_apply]
  change (∑ r : Fin (polynomialFamilyDegree n), ε ^ (r.val+1) *
      (Expression.sumFinset Finset.univ (fun i => padTensorPolynomial (P i) k r)).eval G
        (planeCoordinateIsometry.symm p,t)) =
    ∑ i, coordinatePolynomialValue (P i) ε G t p k
  simp_rw [Expression.eval_sumFinset,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (padTensorPolynomial_value (P i)
    (le_polynomialFamilyDegree n i) ε G t) p) k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
