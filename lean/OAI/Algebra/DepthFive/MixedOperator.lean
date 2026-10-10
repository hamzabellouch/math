import Mathlib

namespace OAI

/-! The full differentiation/multiplication substitution used by the rank measure.
The variables selected by `isV` act by partial differentiation; all others
act by multiplication. Since these two sets are disjoint, the operators
commute, and polynomial substitution is an algebra homomorphism. -/

noncomputable section

namespace Problem335

open MvPolynomial

universe u v
variable {K : Type u} [CommSemiring K] {σ : Type v}

/-- Formal partial derivatives commute, over an arbitrary commutative semiring. -/
theorem pderiv_pderiv_comm (i j : σ) (p : MvPolynomial σ K) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases h : i = j
  · subst j; rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    ite_eq_right h, ite_eq_right (Ne.symm h), add_zero]
  rw [add_right_comm m (Finsupp.single i 1) (Finsupp.single j 1)]
  ring

/-- The endomorphism assigned to an individual variable. -/
def variableOperator (isV : σ → Bool) (i : σ) :
    Module.End K (MvPolynomial σ K) :=
  if isV i then (pderiv i).toLinearMap else LinearMap.mulLeft K (X i)

@[simp] theorem variableOperator_of_true (isV : σ → Bool) (i : σ)
    (h : isV i = true) (p : MvPolynomial σ K) :
    variableOperator isV i p = pderiv i p := by
  simp [variableOperator, h]

@[simp] theorem variableOperator_of_false (isV : σ → Bool) (i : σ)
    (h : isV i = false) (p : MvPolynomial σ K) :
    variableOperator isV i p = X i * p := by
  simp [variableOperator, h]

/-- Operators assigned to any two variables commute. -/
theorem variableOperator_comm (isV : σ → Bool) (i j : σ) :
    Commute (variableOperator (K := K) isV i) (variableOperator isV j) := by
  classical
  change variableOperator isV i * variableOperator isV j =
    variableOperator isV j * variableOperator isV i
  apply LinearMap.ext
  intro p
  change variableOperator isV i (variableOperator isV j p) =
    variableOperator isV j (variableOperator isV i p)
  cases hi : isV i <;> cases hj : isV j
  · simp [variableOperator, hi, hj, mul_left_comm]
  · have hij : i ≠ j := by intro h; subst j; simp_all
    simp [variableOperator, hi, hj, pderiv_X_of_ne hij]
  · have hji : j ≠ i := by intro h; subst j; simp_all
    simp [variableOperator, hi, hj, pderiv_X_of_ne hji]
  · simpa [variableOperator, hi, hj] using pderiv_pderiv_comm i j p

open scoped IsMulCommutative in
/-- Substitution of derivatives on `V` and multiplication on its complement.
This is the full operator, before taking a bidegree component or restricting
to finite-dimensional homogeneous source and target spaces. -/
def mixedOperator (isV : σ → Bool) :
    MvPolynomial σ K →ₐ[K] Module.End K (MvPolynomial σ K) := by
  let A := Algebra.adjoin K (Set.range (variableOperator (K := K) isV))
  let : IsMulCommutative A := Algebra.isMulCommutative_adjoin K (by
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩ _
    exact variableOperator_comm (K := K) isV i j)
  exact A.val.comp (MvPolynomial.aeval fun i =>
    (⟨variableOperator isV i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ : A))

@[simp] theorem mixedOperator_X (isV : σ → Bool) (i : σ) :
    mixedOperator (K := K) isV (X i) = variableOperator isV i := by
  simp [mixedOperator]

@[simp] theorem mixedOperator_C (isV : σ → Bool) (a : K) :
    mixedOperator isV (C a) = a • (1 : Module.End K (MvPolynomial σ K)) := by
  simp [mixedOperator, Algebra.algebraMap_eq_smul_one]

@[simp] theorem mixedOperator_add (isV : σ → Bool) (p q : MvPolynomial σ K) :
    mixedOperator isV (p + q) = mixedOperator isV p + mixedOperator isV q :=
  map_add _ _ _

/-- The full operator respects products (unlike the projected finite rank map). -/
@[simp] theorem mixedOperator_mul (isV : σ → Bool) (p q : MvPolynomial σ K) :
    mixedOperator isV (p * q) = mixedOperator isV p * mixedOperator isV q :=
  map_mul _ _ _

theorem mixedOperator_mul_apply (isV : σ → Bool) (p q f : MvPolynomial σ K) :
    mixedOperator isV (p * q) f = mixedOperator isV p (mixedOperator isV q f) := by
  rw [mixedOperator_mul]
  rfl

end Problem335

end

end OAI
