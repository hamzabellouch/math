import Mathlib
import OAI.Analysis.LaughlinFock.NormalOrdering

namespace OAI

/-! Three Gram. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder

 
theorem pair_creator_commutator (Q : ℕ) (i j k : Orbital Q) :
    (annihilator Q j * annihilator Q i) * creator Q k =
      creator Q k * (annihilator Q j * annihilator Q i) +
        (if i=k then annihilator Q j else 0) -
        (if j=k then annihilator Q i else 0) := by
  have hi := eq_sub_of_add_eq (annihilator_creator_anticommute Q i k)
  have hj := eq_sub_of_add_eq (annihilator_creator_anticommute Q j k)
  rw [Matrix.mul_assoc, hi, Matrix.mul_sub, ← Matrix.mul_assoc _ (creator Q k), hj]
  split_ifs <;> simp only [Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.sub_mul] <;> noncomm_ring

 
def pairPartialAnnihilator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ) (k : Orbital Q) :
    FockMatrix Q := ∑ i, a k i • annihilator Q i

 
theorem coefficientPair_creator_commutator (Q : ℕ) (a : Orbital Q → Orbital Q → ℂ)
    (ha : ∀ i j, a j i = -a i j) (k : Orbital Q) :
    coefficientPairAnnihilator Q a * creator Q k =
      creator Q k * coefficientPairAnnihilator Q a + pairPartialAnnihilator Q a k := by
  classical
  have hdiag : a k k = 0 := by have h := ha k k; linear_combination (1 / 2 : ℂ) * h
  have hsum : (∑ i : Orbital Q, ∑ j : Orbital Q,
      if i<j then a i j • ((if i=k then annihilator Q j else 0) -
        (if j=k then annihilator Q i else 0)) else 0) = pairPartialAnnihilator Q a k := by
    have ht (i j : Orbital Q) :
        (if i<j then a i j • ((if i=k then annihilator Q j else 0) -
          (if j=k then annihilator Q i else 0)) else 0) =
        (if i=k then (if i<j then a i j • annihilator Q j else 0) else 0) -
        (if j=k then (if i<j then a i j • annihilator Q i else 0) else 0) := by
      split_ifs <;> simp only [smul_sub, smul_zero, smul_neg, zero_sub, sub_zero]
    simp only [ht, Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f := fun i j : Orbital Q =>
      if i=k then (if i<j then a i j • annihilator Q j else 0) else 0)]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_sub_distrib]
    unfold pairPartialAnnihilator
    apply Finset.sum_congr rfl
    intro i _
    rcases lt_trichotomy k i with h | rfl | h
    · simp [h, not_lt.mpr h.le]
    · simp [hdiag]
    · simp [h, not_lt.mpr h.le, ha k i]
  calc
    _ = creator Q k * coefficientPairAnnihilator Q a +
        ∑ i : Orbital Q, ∑ j : Orbital Q,
          if i<j then a i j • ((if i=k then annihilator Q j else 0) -
            (if j=k then annihilator Q i else 0)) else 0 := by
      unfold coefficientPairAnnihilator
      simp only [Matrix.sum_mul, Matrix.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i<j
      · simp only [ite_eq_left hij, Matrix.smul_mul, Matrix.mul_smul, pair_creator_commutator]
        module
      · simp [hij]
    _ = _ := by rw [hsum]

 

theorem pairCoefficient_antisymm (Q p : ℕ) (i j : Orbital Q) :
    pairCoefficient Q p j i = -pairCoefficient Q p i j := by
  simp only [pairCoefficient_eq, Nat.add_comm j.val i.val]
  split_ifs
  · have hs : ((Q.descFactorial j.val : ℝ)*(Q.descFactorial i.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(j.val.factorial : ℝ)*(i.val.factorial : ℝ)) =
      ((Q.descFactorial i.val : ℝ)*(Q.descFactorial j.val : ℝ)*(p.factorial : ℝ)) /
        ((Q : ℝ)*((2*Q-2).descFactorial p : ℝ)*(i.val.factorial : ℝ)*(j.val.factorial : ℝ)) := by ring
    rw [hs]
    ring
  · simp

 
theorem annihilationSpace_entry_eq_zero (Q d : ℕ) (M : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q d) (A B : Occupation Q) (h : A.card+d ≠ B.card) :
    M A B = 0 := by
  classical
  rw [annihilationSpace_normal_form Q d M hM]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro S _
  rw [basisAnnihilator_entry_eq_zero Q S.val A B (by rwa [S.property]), mul_zero]

 

theorem annihilatorVector_gram (Q d : ℕ) (M N : FockMatrix Q)
    (hM : M ∈ AnnihilationSpace Q d) :
    (∑ S : SectorOccupation Q d,
      star (annihilatorVector Q d M S) * annihilatorVector Q d N S) = (M*Nᴴ) ∅ ∅ := by
  classical
  simp only [annihilatorVector, star_star, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    _ = ∑ S ∈ Finset.univ.filter (fun S : Occupation Q => S.card=d), M ∅ S * star (N ∅ S) :=
      (Finset.sum_subtype _ (by intro S; simp) _).symm
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro S _ hS
      rw [annihilationSpace_entry_eq_zero Q d M hM ∅ S (by simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.card_empty, zero_add, eq_comm] using hS), zero_mul]

 
theorem creator_mul_vacuum_zero (Q : ℕ) (k : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (creator Q k * M) ∅ A = 0 := by
  classical
  have hz (B : Occupation Q) : creator Q k ∅ B = 0 := by
    apply ite_eq_right
    rintro ⟨_, h⟩
    have := congrArg (fun S : Occupation Q => k ∈ S) h
    simp at this
  simp only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero]

 
theorem mul_annihilator_vacuum_zero (Q : ℕ) (k : Orbital Q) (M : FockMatrix Q)
    (A : Occupation Q) : (M * annihilator Q k) A ∅ = 0 := by
  rw [mul_annihilator_apply]
  simp

 
theorem annihilator_creator_vacuum (Q : ℕ) (i j : Orbital Q) :
    (annihilator Q i * creator Q j) ∅ ∅ = if i=j then 1 else 0 := by
  rw [annihilator_mul_vacuum]
  simp [creator, fermionSign]

 
theorem pairPartial_vacuum_gram (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ)
    (j k : Orbital Q) :
    (pairPartialAnnihilator Q a k * (pairPartialAnnihilator Q b j)ᴴ) ∅ ∅ =
      ∑ i, a k i * star (b j i) := by
  classical
  simp only [pairPartialAnnihilator, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← creator_eq_adjoint,
    annihilator_creator_vacuum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

 

theorem coefficientTriple_vacuum_gram (Q : ℕ) (a b : Orbital Q → Orbital Q → ℂ)
    (ha : ∀ i j, a j i = -a i j) (hb : ∀ i j, b j i = -b i j)
    (j k : Orbital Q) :
    ((annihilator Q j * coefficientPairAnnihilator Q a) *
      (annihilator Q k * coefficientPairAnnihilator Q b)ᴴ) ∅ ∅ =
      (if j=k then (coefficientPairAnnihilator Q a * (coefficientPairAnnihilator Q b)ᴴ) ∅ ∅ else 0) -
        ∑ i, a k i * star (b j i) := by
  classical
  let M := coefficientPairAnnihilator Q a
  let N := coefficientPairAnnihilator Q b
  have hb' : annihilator Q j * Nᴴ = Nᴴ * annihilator Q j + (pairPartialAnnihilator Q b j)ᴴ := by
    have h := congrArg Matrix.conjTranspose (coefficientPair_creator_commutator Q b hb j)
    simpa only [creator_eq_adjoint, Matrix.conjTranspose_mul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose] using h
  have hex : (M * creator Q k * annihilator Q j * Nᴴ) ∅ ∅ =
      (pairPartialAnnihilator Q a k * (pairPartialAnnihilator Q b j)ᴴ) ∅ ∅ := by
    rw [show M * creator Q k = creator Q k * M + pairPartialAnnihilator Q a k from
      coefficientPair_creator_commutator Q a ha k]
    simp only [Matrix.add_mul, Matrix.add_apply]
    rw [Matrix.mul_assoc (creator Q k), Matrix.mul_assoc (creator Q k), creator_mul_vacuum_zero]
    rw [zero_add, Matrix.mul_assoc, hb', Matrix.mul_add, Matrix.add_apply,
      ← Matrix.mul_assoc _ Nᴴ, mul_annihilator_vacuum_zero, zero_add]
  have hJn : (annihilator Q k * N)ᴴ = creator Q k * Nᴴ := by
    rw [annihilator_commutes_coefficientPair, Matrix.conjTranspose_mul, ← creator_eq_adjoint]
  change ((annihilator Q j * M) * (annihilator Q k * N)ᴴ) ∅ ∅ = _
  rw [hJn, annihilator_commutes_coefficientPair, Matrix.mul_assoc M,
    ← Matrix.mul_assoc (annihilator Q j),
    eq_sub_of_add_eq (annihilator_creator_anticommute Q j k)]
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply]
  rw [← Matrix.mul_assoc M (creator Q k * annihilator Q j),
    ← Matrix.mul_assoc M (creator Q k), hex, pairPartial_vacuum_gram]
  congr 1
  split_ifs <;> simp [M, N]

 
theorem threeWedgeMatrix_gram_apply (Q : ℕ) (hQ : 1 ≤ Q)
    (pj rk : PairLabel Q × Orbital Q) :
    ((threeWedgeMatrix Q)ᴴ * threeWedgeMatrix Q) pj rk =
      (if pj=rk then 1 else 0) -
        ∑ i : Orbital Q, (pairCoefficient Q pj.1.val rk.2 i : ℂ) *
          (pairCoefficient Q rk.1.val pj.2 i : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, threeWedgeMatrix]
  rw [annihilatorVector_gram Q 3 _ _
    (annihilationSpace_mul Q 2 1 (pairAnnihilator_mem Q _)
      (annihilator_mem Q _))]
  have ha (p : ℕ) (i j : Orbital Q) :
      (pairCoefficient Q p j i : ℂ) = -(pairCoefficient Q p i j : ℂ) := by
    rw [pairCoefficient_antisymm, Complex.ofReal_neg]
  rw [pairAnnihilator_eq_coefficientPairAnnihilator,
    pairAnnihilator_eq_coefficientPairAnnihilator, coefficientTriple_vacuum_gram Q _ _ (ha _) (ha _)]
  simp only [Complex.star_def, Complex.conj_ofReal]
  simp only [← pairAnnihilator_eq_coefficientPairAnnihilator]
  rw [← annihilatorVector_gram Q 2 (pairAnnihilator Q pj.1.val) (pairAnnihilator Q rk.1.val)
    (pairAnnihilator_mem Q _)]
  change (if pj.2=rk.2 then
    (∑ S, star (pairVector Q pj.1.val S) * pairVector Q rk.1.val S) else 0) - _ = _
  rw [pairVector_orthonormal Q _ _ hQ (by have := pj.1.isLt; omega)]
  congr 1
  simp only [Prod.ext_iff, Fin.val_inj, ← ite_and, and_comm]

end LaughlinFock
end

end OAI
