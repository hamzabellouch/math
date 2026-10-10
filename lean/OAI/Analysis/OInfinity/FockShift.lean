import OAI.Analysis.OInfinity.FockReturn

namespace OAI

/-! # The finite Fock compression on a canonical generator -/

noncomputable section
open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace WeakPureInfiniteness

lemma finiteFockWord_length {N m : ℕ} (i : FiniteFockIndex N m) :
    (finiteFockWord i).length = i.1.val := List.length_ofFn

def finiteFockCons {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (hj : j.1.val < m) : FiniteFockIndex N m :=
  ⟨⟨j.1.val + 1, by omega⟩, Fin.cons p j.2⟩

lemma finiteFockWord_cons {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (hj : j.1.val < m) :
    finiteFockWord (finiteFockCons p j hj) = p.val :: finiteFockWord j := by
  simp [finiteFockWord, finiteFockCons, List.ofFn_succ]

lemma finiteFockAlgebraWord_cons {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (hj : j.1.val < m) :
    finiteFockAlgebraWord (finiteFockCons p j hj) =
      oInfinityIsometry p * finiteFockAlgebraWord j :=
  oInfinityPositiveWord_cons N j.1.val p j.2

lemma oInfinityFockCompression_generator {N m : ℕ} (p : Fin N)
    (i j : FiniteFockIndex N m) :
    oInfinityFockCompression N m (oInfinityIsometry p) i j =
      if finiteFockWord i = p.val :: finiteFockWord j then 1 else 0 := by
  rw [oInfinityFockCompression_apply]
  change inner ℂ (lp.single 2 (finiteFockWord i) 1)
    (fockShift p (lp.single 2 (finiteFockWord j) 1)) = _
  rw [fockShift_single, lp.inner_single_left, lp.single_apply]
  simp [Pi.single_apply]

lemma sum_finiteFock_prefix {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (f : FiniteFockIndex N m → OInfinity) (hj : j.1.val < m) :
    (∑ i, (if finiteFockWord i = p.val :: finiteFockWord j then (1 : ℂ) else 0) • f i) =
      f (finiteFockCons p j hj) := by
  have he (i : FiniteFockIndex N m) :
      finiteFockWord i = p.val :: finiteFockWord j ↔ i = finiteFockCons p j hj := by
    rw [← finiteFockWord_cons p j hj]
    exact (finiteFockWord_injective N m).eq_iff
  simp only [he, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

lemma sum_finiteFock_prefix_boundary {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (f : FiniteFockIndex N m → OInfinity) (hj : ¬j.1.val < m) :
    (∑ i, (if finiteFockWord i = p.val :: finiteFockWord j then (1 : ℂ) else 0) • f i) = 0 := by
  have he (i : FiniteFockIndex N m) : finiteFockWord i ≠ p.val :: finiteFockWord j := by
    intro h
    have hh := congrArg List.length h
    simp only [finiteFockWord_length, List.length_cons] at hh
    have hi := i.1.isLt
    omega
  simp [he]

lemma unweightedFockReturn_generator_sum {N m : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockUnweightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p)) =
      ∑ j : FiniteFockIndex N m, if j.1.val < m then
        oInfinityIsometry p * finiteFockAlgebraWord j * star (finiteFockAlgebraWord j) else 0 := by
  rw [cuntzGramMap_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [oInfinityFockCompression_generator]
  by_cases hj : j.1.val < m
  · rw [sum_finiteFock_prefix p j _ hj, ite_eq_left hj]
    simp only [finiteFockUnweightedCoefficient, star_star, finiteFockAlgebraWord_cons]
  · rw [sum_finiteFock_prefix_boundary p j _ hj, ite_eq_right hj]

lemma unweightedFockReturn_generator {N m : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockUnweightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p)) =
      oInfinityIsometry p * ∑ k ∈ Finset.range m, oInfinityLevel N k := by
  rw [unweightedFockReturn_generator_sum]
  simp only [Fintype.sum_sigma, finiteFockAlgebraWord]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have hlast : (∑ w : Fin m → Fin N,
      if m < m then oInfinityIsometry p * oInfinityPositiveWord N w *
        star (oInfinityPositiveWord N w) else 0) = 0 := by simp
  rw [hlast, add_zero]
  have hlevel (k : Fin m) : (∑ w : Fin k.val → Fin N,
      if k.val < m then oInfinityIsometry p * oInfinityPositiveWord N w *
        star (oInfinityPositiveWord N w) else 0) =
      oInfinityIsometry p * oInfinityLevel N k.val := by
    simp only [ite_eq_left k.isLt, mul_assoc, ← Finset.mul_sum]
    rw [oInfinityPositiveWord_sum_range]
  simp only [hlevel, ← Finset.mul_sum,
    Fin.sum_univ_eq_sum_range]

lemma weightedFockCoefficient_prefix {N m : ℕ} (p : Fin N) (j : FiniteFockIndex N m)
    (hj : j.1.val < m) :
    star (finiteFockWeightedCoefficient (finiteFockCons p j hj)) *
      finiteFockWeightedCoefficient j =
      (((Real.sqrt ((m : ℝ) - (j.1.val + 1)) *
        Real.sqrt ((m : ℝ) - j.1.val) : ℝ)) : ℂ) •
      (oInfinityIsometry p * finiteFockAlgebraWord j * oInfinityFiniteVacuum N *
        star (finiteFockAlgebraWord j)) := by
  have hbase : star (oInfinityFiniteVacuum N *
        star (finiteFockAlgebraWord (finiteFockCons p j hj))) *
      (oInfinityFiniteVacuum N * star (finiteFockAlgebraWord j)) =
      oInfinityIsometry p * finiteFockAlgebraWord j * oInfinityFiniteVacuum N *
        star (finiteFockAlgebraWord j) := by
    rw [star_mul, star_star, oInfinityFiniteVacuum_star, finiteFockAlgebraWord_cons]
    calc
      _ = oInfinityIsometry p * finiteFockAlgebraWord j *
          (oInfinityFiniteVacuum N * oInfinityFiniteVacuum N) *
          star (finiteFockAlgebraWord j) := by noncomm_ring
      _ = _ := by rw [oInfinityFiniteVacuum_idempotent]
  simp only [finiteFockWeightedCoefficient, star_smul, smul_mul_smul_comm,
    Complex.star_def, Complex.conj_ofReal, hbase, Complex.ofReal_mul]
  simp only [finiteFockCons, Nat.cast_add, Nat.cast_one]

lemma weightedFockReturn_generator_sum {N m : ℕ} (p : Fin N) :
    cuntzGramMap (finiteFockCuntzFamily N m) (finiteFockCuntzFamily_relations N m)
      finiteFockWeightedCoefficient (oInfinityFockCompression N m (oInfinityIsometry p)) =
      ∑ j : FiniteFockIndex N m, if j.1.val < m then
        (((Real.sqrt ((m : ℝ) - (j.1.val + 1)) *
          Real.sqrt ((m : ℝ) - j.1.val) : ℝ)) : ℂ) •
        (oInfinityIsometry p * finiteFockAlgebraWord j * oInfinityFiniteVacuum N *
          star (finiteFockAlgebraWord j)) else 0 := by
  rw [cuntzGramMap_apply, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [oInfinityFockCompression_generator]
  by_cases hj : j.1.val < m
  · rw [sum_finiteFock_prefix p j _ hj, ite_eq_left hj,
      weightedFockCoefficient_prefix p j hj]
  · rw [sum_finiteFock_prefix_boundary p j _ hj, ite_eq_right hj]

end WeakPureInfiniteness

end

end OAI
