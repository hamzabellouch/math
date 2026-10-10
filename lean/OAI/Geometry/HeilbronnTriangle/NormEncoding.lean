import OAI.Geometry.HeilbronnTriangle.FiniteFieldLabels
import OAI.Geometry.HeilbronnTriangle.NormHomogeneity
import OAI.Geometry.HeilbronnTriangle.MonomialCount
import OAI.Geometry.HeilbronnTriangle.PolynomialCoefficients
import OAI.Geometry.HeilbronnTriangle.TripleEnumeration

namespace OAI


noncomputable section

namespace Problem355.NormEncoding

open scoped BigOperators
open MvPolynomial

abbrev Coordinate := Fin 3 × Fin heilbronnD

def monomialExponent (i : Fin heilbronnM) : Coordinate →₀ ℕ :=
  (Monomials.heilbronnCoordinateMonomialEquiv.symm i).val

theorem monomialExponent_injective : Function.Injective monomialExponent :=
  Subtype.val_injective.comp Monomials.heilbronnCoordinateMonomialEquiv.symm.injective

variable (p : ℕ) [Fact p.Prime]

theorem monomialExponent_covers (d : (Fin 3 × Coordinate) →₀ ℕ)
    (hd : d ∈ (FiniteFieldLabels.labelNormPolynomial p).support) (j : Fin 3) :
    d.curry j ∈ Set.range monomialExponent := by
  have hdegree : (d.curry j).degree = heilbronnD := by
    rw [PolynomialCoefficients.curry_degree_eq_weight]
    change Finsupp.weight (NormHomogeneity.groupWeight j) d = heilbronnD
    have h := NormHomogeneity.normDeterminantPolynomial_isWeightedHomogeneous
      (FiniteFieldLabels.labelBasis p) j
      (MvPolynomial.mem_support_iff.mp hd)
    simpa only [FiniteFieldLabels.finrank_label] using h
  let m : Monomials.DegreeIndex Coordinate heilbronnD := ⟨d.curry j, hdegree⟩
  refine ⟨Monomials.heilbronnCoordinateMonomialEquiv m, ?_⟩
  simp [monomialExponent, m]

def normCoefficient (i j k : Fin heilbronnM) : ZMod p :=
  PolynomialCoefficients.tensorCoeff (FiniteFieldLabels.labelNormPolynomial p)
    (monomialExponent i) (monomialExponent j) (monomialExponent k)

def monomialValue (i : Fin heilbronnM) (x : FiniteFieldLabels.Label p) : ZMod p :=
  MvPolynomial.eval (FiniteFieldLabels.labelVector p x) (monomial (monomialExponent i) 1)

theorem normCoefficient_swap01 (i j k : Fin heilbronnM) :
    normCoefficient p j i k = -normCoefficient p i j k := by
  apply PolynomialCoefficients.tensorCoeff_swap01
  exact FiniteFieldLabels.swap_labelNormPolynomial p (by decide : (0 : Fin 3) ≠ 1)

theorem normCoefficient_swap12 (i j k : Fin heilbronnM) :
    normCoefficient p i k j = -normCoefficient p i j k := by
  apply PolynomialCoefficients.tensorCoeff_swap12
  exact FiniteFieldLabels.swap_labelNormPolynomial p (by decide : (1 : Fin 3) ≠ 2)

theorem eval_labelNormPolynomial_eq_sum (x y z : FiniteFieldLabels.Label p) :
    MvPolynomial.eval (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)
      (FiniteFieldLabels.labelNormPolynomial p) =
      ∑ i, ∑ j, ∑ k, normCoefficient p i j k * monomialValue p i x *
        monomialValue p j y * monomialValue p k z := by
  simpa [normCoefficient, PolynomialCoefficients.tensorCoeff, monomialValue] using
    PolynomialCoefficients.eval_three_group_expansion
      (FiniteFieldLabels.labelNormPolynomial p) monomialExponent monomialExponent_injective
      (monomialExponent_covers p)
      (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)

theorem two_ne_zero (hp : 2 < p) : (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  intro h
  exact Nat.not_dvd_of_pos_of_lt (by decide) hp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h)

private theorem eq_zero_of_eq_neg {R : Type*} [CommRing R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (a : R) (ha : a = -a) : a = 0 := by
  have h : (2 : R) * a = 0 := by linear_combination ha
  exact (mul_eq_zero.mp h).resolve_left h2

theorem normCoefficient_diag01 (hp : 2 < p) (i k : Fin heilbronnM) :
    normCoefficient p i i k = 0 :=
  eq_zero_of_eq_neg (two_ne_zero p hp) _ (normCoefficient_swap01 p i i k)

theorem normCoefficient_diag12 (hp : 2 < p) (i j : Fin heilbronnM) :
    normCoefficient p i j j = 0 :=
  eq_zero_of_eq_neg (two_ne_zero p hp) _ (normCoefficient_swap12 p i j j)

theorem normCoefficient_diag02 (hp : 2 < p) (i j : Fin heilbronnM) :
    normCoefficient p i j i = 0 := by
  rw [normCoefficient_swap01, normCoefficient_diag12 p hp, neg_zero]

def determinantIndexEquiv :
    Fin (Nat.choose (Fintype.card (Fin heilbronnM)) 3) ≃ Fin heilbronnT :=
  finCongr (by rw [Fintype.card_fin]; rfl)

def normRowFunctions (i : Fin 3) (a : Fin heilbronnT)
    (x : FiniteFieldLabels.Label p) : ZMod p :=
  NormDecomposition.decompositionRows (normCoefficient p) (monomialValue p)
    (determinantIndexEquiv.symm a) i x

private theorem matrix_of_label_values {R X : Type*} (f : Fin 3 → X → R) (x y z : X) :
    (fun i j => f i (![x, y, z] j)) =
      !![f 0 x, f 0 y, f 0 z; f 1 x, f 1 y, f 1 z; f 2 x, f 2 y, f 2 z] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem sum_normRowFunctions_eq_eval (hp : 2 < p) (x y z : FiniteFieldLabels.Label p) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => normRowFunctions p i a (![x, y, z] j))) =
      MvPolynomial.eval (fun v => FiniteFieldLabels.labelVector p (![x, y, z] v.1) v.2)
        (FiniteFieldLabels.labelNormPolynomial p) := by
  have h := NormDecomposition.alternating_sum_eq_sum_determinants
    (normCoefficient p) (monomialValue p)
    (normCoefficient_diag01 p hp) (normCoefficient_diag02 p hp)
    (normCoefficient_diag12 p hp) (normCoefficient_swap01 p)
    (normCoefficient_swap12 p) x y z
  rw [← eval_labelNormPolynomial_eq_sum p x y z] at h
  rw [h]
  simp_rw [normRowFunctions, matrix_of_label_values]
  apply Fintype.sum_equiv determinantIndexEquiv.symm
  intro a
  rfl

theorem sum_normRowFunctions_ne_zero (hp : 2 < p)
    {x y z : FiniteFieldLabels.Label p} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (∑ a : Fin heilbronnT,
      Matrix.det (fun i j => normRowFunctions p i a (![x, y, z] j))) ≠ 0 := by
  rw [sum_normRowFunctions_eq_eval p hp]
  exact FiniteFieldLabels.eval_labelNormPolynomial_ne_zero p hxy hxz hyz

theorem exists_norm_summands (hp : 2 < p) :
    ∃ f : Fin 3 → Fin heilbronnT → FiniteFieldLabels.Label p → ZMod p,
      ∀ x y z, x ≠ y → x ≠ z → y ≠ z →
        (∑ a : Fin heilbronnT, Matrix.det (fun i j => f i a (![x, y, z] j))) ≠ 0 := by
  exact ⟨normRowFunctions p, fun _ _ _ hxy hxz hyz =>
    sum_normRowFunctions_ne_zero p hp hxy hxz hyz⟩

end Problem355.NormEncoding

end

end OAI
