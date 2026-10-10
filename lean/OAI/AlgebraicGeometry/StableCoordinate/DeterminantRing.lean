import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace OAI

/-!
# The determinant ring used in the coordinate obstruction

The independent variables are ordered `a,d,b,c,u`.  The only relation is
`a*c-b*d=1`.  This module records the quotient and its elementary universal
property; it makes no domain, localization, or rigidity assertion by assumption.
-/

namespace StableCoordinate.DeterminantRing

open MvPolynomial

variable (k : Type*) [CommRing k]

abbrev P := MvPolynomial (Fin 5) k

noncomputable def relation : P k := X 0 * X 3 - X 2 * X 1 - 1
noncomputable def relationIdeal : Ideal (P k) := Ideal.span {relation k}
abbrev C := P k ⧸ relationIdeal k

noncomputable def mk : P k →ₐ[k] C k := Ideal.Quotient.mkₐ k (relationIdeal k)
noncomputable def generator (i : Fin 5) : C k := mk k (X i)
noncomputable abbrev a : C k := generator k 0
noncomputable abbrev d : C k := generator k 1
noncomputable abbrev b : C k := generator k 2
noncomputable abbrev c : C k := generator k 3
noncomputable abbrev u : C k := generator k 4

@[simp] theorem mk_relation : mk k (relation k) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem determinant_relation : a k * c k - b k * d k = 1 := by
  have h := mk_relation k
  simp only [relation, map_sub, map_mul, map_one] at h
  exact sub_eq_zero.mp h

variable {k}
variable {S : Type*} [CommRing S] [Algebra k S]

/-- The universal homomorphism out of the determinant quotient. -/
noncomputable def lift (A D B C U : S) (h : A * C - B * D = 1) :
    DeterminantRing.C k →ₐ[k] S :=
  Ideal.Quotient.liftₐ (relationIdeal k) (aeval ![A, D, B, C, U]) (by
    intro p hp
    have hs : relationIdeal k ≤ RingHom.ker (aeval ![A, D, B, C, U]).toRingHom := by
      rw [relationIdeal, Ideal.span_singleton_le_iff_mem]
      simp [RingHom.mem_ker, relation, h]
    exact hs hp)

@[simp] theorem lift_mk (A D B C U : S) (h : A * C - B * D = 1) (p : P k) :
    lift A D B C U h (mk k p) = aeval ![A, D, B, C, U] p := rfl

@[simp] theorem lift_a (A D B C U : S) (h : A * C - B * D = 1) :
    lift A D B C U h (a k) = A := by simp [a, generator]
@[simp] theorem lift_d (A D B C U : S) (h : A * C - B * D = 1) :
    lift A D B C U h (d k) = D := by simp [d, generator]
@[simp] theorem lift_b (A D B C U : S) (h : A * C - B * D = 1) :
    lift A D B C U h (b k) = B := by simp [b, generator]
@[simp] theorem lift_c (A D B C U : S) (h : A * C - B * D = 1) :
    lift A D B C U h (c k) = C := by simp [c, generator]
@[simp] theorem lift_u (A D B C U : S) (h : A * C - B * D = 1) :
    lift A D B C U h (u k) = U := by simp [u, generator]

@[ext] theorem hom_ext {f g : DeterminantRing.C k →ₐ[k] S}
    (ha : f (a k) = g (a k)) (hd : f (d k) = g (d k))
    (hb : f (b k) = g (b k)) (hc : f (c k) = g (c k))
    (hu : f (u k) = g (u k)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact ha
  · exact hd
  · exact hb
  · exact hc
  · exact hu

/-- The three-variable polynomial subalgebra appearing in the rigidity proof. -/
abbrev Base (k : Type*) [CommRing k] := MvPolynomial (Fin 3) k

/-- The base variables have order `a,d,u`. -/
noncomputable def baseMap : Base k →ₐ[k] DeterminantRing.C k :=
  aeval ![a k, d k, u k]

/-- The canonical polynomial coefficient-algebra structure, induced by `baseMap`. -/
noncomputable instance baseAlgebra : Algebra (Base k) (DeterminantRing.C k) :=
  baseMap.toRingHom.toAlgebra

instance baseScalarTower : IsScalarTower k (Base k) (DeterminantRing.C k) :=
  IsScalarTower.of_algHom (baseMap (k := k))

@[simp] theorem base_algebraMap (r : Base k) :
    algebraMap (Base k) (DeterminantRing.C k) r = baseMap r := rfl

@[simp] theorem baseMap_X0 : baseMap (X 0 : Base k) = a k := by simp [baseMap]
@[simp] theorem baseMap_X1 : baseMap (X 1 : Base k) = d k := by simp [baseMap]
@[simp] theorem baseMap_X2 : baseMap (X 2 : Base k) = u k := by simp [baseMap]

end StableCoordinate.DeterminantRing

end OAI
