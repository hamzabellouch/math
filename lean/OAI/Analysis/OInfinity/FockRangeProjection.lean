import OAI.Analysis.OInfinity.FockConvergence

namespace OAI

/-! # Range projections in the finite Fock approximation -/

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

local instance : PartialOrder OInfinity := CStarAlgebra.spectralOrder _
local instance : StarOrderedRing OInfinity := CStarAlgebra.spectralOrderedRing _
local instance : DistribSMul ℂ OInfinity :=
  @DistribMulAction.toDistribSMul ℂ OInfinity _ _
    (@Module.toDistribMulAction ℂ OInfinity _ _ inferInstance)
local instance rangeComplexScalars : SMulWithZero ℂ OInfinity :=
  @MulActionWithZero.toSMulWithZero ℂ OInfinity _ _
    (@Module.toMulActionWithZero ℂ OInfinity _ _ inferInstance)
local instance : Algebra ℝ OInfinity := Algebra.compHom OInfinity Complex.ofRealHom
local instance : Module ℝ OInfinity := Module.complexToReal _
local instance : DistribSMul ℝ OInfinity :=
  @DistribMulAction.toDistribSMul ℝ OInfinity _ _
    (@Module.toDistribMulAction ℝ OInfinity _ _ (Module.complexToReal _))

lemma fockShift_adjoint_single_cons (p q : ℕ) (w : List ℕ) :
    (fockShift p).toContinuousLinearMap.adjoint (lp.single 2 (q :: w) 1) =
      if p = q then lp.single 2 w 1 else 0 := by
  ext v
  rw [fockShift_adjoint_apply]
  by_cases hpq : p = q
  · subst q
    simp [lp.single_apply, Pi.single_apply]
  · simp [lp.single_apply, hpq]

lemma fockShift_adjoint_single_nil (p : ℕ) :
    (fockShift p).toContinuousLinearMap.adjoint (lp.single 2 ([] : List ℕ) 1) = 0 := by
  ext v
  simp [fockShift_adjoint_apply, lp.single_apply]

lemma fockRangeProjection_single (p : ℕ) (w : List ℕ) :
    fockShift p ((fockShift p).toContinuousLinearMap.adjoint (lp.single 2 w 1)) =
      if w.head? = some p then lp.single 2 w 1 else 0 := by
  cases w with
  | nil => simp [fockShift_adjoint_single_nil]
  | cons q w =>
    rw [fockShift_adjoint_single_cons]
    by_cases hpq : p = q
    · subst q; simp
    · simp [hpq, Ne.symm hpq]

lemma oInfinityFockCompression_rangeProjection {N m : ℕ} (p : Fin N)
    (i j : FiniteFockIndex N m) :
    oInfinityFockCompression N m (oInfinityIsometry p * star (oInfinityIsometry p)) i j =
      if (finiteFockWord j).head? = some p.val then (if i = j then 1 else 0) else 0 := by
  rw [oInfinityFockCompression_apply]
  change inner ℂ (lp.single 2 (finiteFockWord i) 1)
    (fockShift p ((fockShift p).toContinuousLinearMap.adjoint
      (lp.single 2 (finiteFockWord j) 1))) = _
  rw [fockRangeProjection_single]
  by_cases hj : (finiteFockWord j).head? = some p.val
  · simp only [ite_eq_left hj, lp.inner_single_left, lp.single_apply]
    have he : finiteFockWord i = finiteFockWord j ↔ i = j :=
      (finiteFockWord_injective N m).eq_iff
    simp [Pi.single_apply, he]
  · simp [hj]

lemma fockRangeReturn_sum {N m : ℕ} (p : Fin N) (c : FiniteFockIndex N m → OInfinity) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m) c
      (oInfinityFockCompression N m (oInfinityIsometry p * star (oInfinityIsometry p))) =
      ∑ j : FiniteFockIndex N m,
        if (finiteFockWord j).head? = some p.val then star (c j) * c j else 0 := by
  rw [cuntzGramMap_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [oInfinityFockCompression_rangeProjection]
  by_cases hj : (finiteFockWord j).head? = some p.val
  · simp [hj]
  · simp [hj]

private lemma sum_fock_cons {M : Type*} [AddCommMonoid M] (N k : ℕ)
    (f : (Fin (k + 1) → Fin N) → M) :
    (∑ w, f w) = ∑ i : Fin N, ∑ w : Fin k → Fin N, f (Fin.cons i w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => Fin N)).sum_comp]
  exact Fintype.sum_prod_type _

lemma sum_finiteFock_rangePrefix {N m : ℕ} (p : Fin N)
    (g : ℕ → OInfinity → OInfinity) :
    (∑ j : FiniteFockIndex N m,
      if (finiteFockWord j).head? = some p.val then
        g j.1.val (finiteFockAlgebraWord j) else 0) =
      ∑ k : Fin m, ∑ w : Fin k.val → Fin N,
        g (k.val + 1) (oInfinityIsometry p * oInfinityPositiveWord N w) := by
  simp only [Fintype.sum_sigma, finiteFockWord, finiteFockAlgebraWord]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, List.ofFn_zero, List.head?_nil, reduceCtorEq,
    ite_false, Finset.sum_const_zero, zero_add, Fin.val_succ]
  apply Finset.sum_congr rfl
  intro k _
  rw [sum_fock_cons]
  have he (q : Fin N) : (some q.val = some p.val) ↔ q = p := by
    simp only [Option.some.injEq, Fin.val_inj]
  simp only [List.ofFn_succ, Fin.cons_zero, List.head?_cons, he,
    oInfinityPositiveWord_cons]
  simp

lemma unweightedFockReturn_rangeProjection {N m : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockUnweightedCoefficient
      (oInfinityFockCompression N m (oInfinityIsometry p * star (oInfinityIsometry p))) =
      oInfinityIsometry p * (∑ k ∈ Finset.range m, oInfinityLevel N k) *
        star (oInfinityIsometry p) := by
  rw [fockRangeReturn_sum]
  simp only [finiteFockUnweightedCoefficient, star_star]
  rw [sum_finiteFock_rangePrefix p (fun _ a => a * star a)]
  simp only [star_mul]
  have hlevel (k : Fin m) :
      (∑ w : Fin k.val → Fin N,
        (oInfinityIsometry p * oInfinityPositiveWord N w) *
          (star (oInfinityPositiveWord N w) * star (oInfinityIsometry p))) =
      oInfinityIsometry p * oInfinityLevel N k.val * star (oInfinityIsometry p) := by
    rw [← oInfinityPositiveWord_sum_range, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    noncomm_ring
  simp only [hlevel, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  exact Fin.sum_univ_eq_sum_range (fun k => oInfinityLevel N k) m

lemma weightedFockReturn_rangeProjection {N r : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N (r + 1))
      (finiteFockCuntzFamily_relations N (r + 1)) finiteFockWeightedCoefficient
      (oInfinityFockCompression N (r + 1)
        (oInfinityIsometry p * star (oInfinityIsometry p))) =
      oInfinityIsometry p *
        (∑ k ∈ Finset.range (r + 1), ((r : ℝ) - k) • oInfinityLevelDifference N k) *
          star (oInfinityIsometry p) := by
  rw [fockRangeReturn_sum]
  simp only [finiteFockWeightedCoefficient_square]
  rw [sum_finiteFock_rangePrefix p (fun k a =>
    (((r + 1 : ℕ) : ℝ) - k) • (a * oInfinityFiniteVacuum N * star a))]
  have hlevel (k : Fin (r + 1)) :
      (∑ w : Fin k.val → Fin N,
        (((r + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ)) •
          ((oInfinityIsometry p * oInfinityPositiveWord N w) * oInfinityFiniteVacuum N *
            star (oInfinityIsometry p * oInfinityPositiveWord N w))) =
      oInfinityIsometry p * (((r : ℝ) - k.val) • oInfinityLevelDifference N k.val) *
        star (oInfinityIsometry p) := by
    have hc : (((r + 1 : ℕ) : ℝ) - ((k.val + 1 : ℕ) : ℝ)) =
        (r : ℝ) - k.val := by push_cast; ring
    rw [hc, ← oInfinityPositiveWord_sum_vacuum, Finset.smul_sum,
      Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    rw [mul_smul_comm, smul_mul_assoc, star_mul]
    congr 1
  simp only [hlevel, ← Finset.sum_mul, ← Finset.mul_sum]
  congr 2
  exact Fin.sum_univ_eq_sum_range
    (fun k => ((r : ℝ) - k) • oInfinityLevelDifference N k) (r + 1)

lemma oInfinityFockApproximation_rangeProjection_succ {N r : ℕ} (p : Fin N) :
    oInfinityFockApproximation N (r + 1)
      (oInfinityIsometry p * star (oInfinityIsometry p)) =
      ((((r : ℝ) + 1) / ((r : ℝ) + 2)) : ℝ) •
        (oInfinityIsometry p * star (oInfinityIsometry p)) := by
  change (((((r + 1 : ℕ) : ℝ) + 1)⁻¹ : ℝ) : ℂ) •
    (cuntzGramMap (finiteFockCuntzFamily N (r + 1))
        (finiteFockCuntzFamily_relations N (r + 1)) finiteFockUnweightedCoefficient
        (oInfinityFockCompression N (r + 1) _) +
      cuntzGramMap (finiteFockCuntzFamily N (r + 1))
        (finiteFockCuntzFamily_relations N (r + 1)) finiteFockWeightedCoefficient
        (oInfinityFockCompression N (r + 1) _)) = _
  rw [unweightedFockReturn_rangeProjection, weightedFockReturn_rangeProjection]
  rw [← add_mul, ← mul_add, oInfinityLevel_weighted_sum]
  rw [mul_smul_comm, smul_mul_assoc, mul_one]
  change ((((r + 1 : ℕ) : ℝ) + 1)⁻¹) •
    (((r : ℝ) + 1) • (oInfinityIsometry p * star (oInfinityIsometry p))) = _
  rw [smul_smul]
  congr 1
  push_cast
  ring

end WeakPureInfiniteness

end

end OAI
