import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Fintype.Basic

namespace OAI

universe uI uG uH

/-!
# Alternating products over literal finite subsets

The exponent is `(-1)^card S`. Pairing subsets along `p` follows from the
powerset decomposition, with the quotient orientation `x S / x (insert p S)`.

The definition and pairing are valid in a division commutative monoid, so they
apply both to actual field values and to units. Cancellation of a constant
family is stated in a commutative group. No local comparison, nonvanishing,
integrality, or torsion statement is assumed or inferred.
-/

namespace CirculantHadamard

open scoped BigOperators

variable {I : Type uI}

def subsetSign (S : Finset I) : ℤ := (-1) ^ S.card

@[simp] theorem subsetSign_empty : subsetSign (∅ : Finset I) = 1 := by
  simp [subsetSign]

theorem subsetSign_of_even (S : Finset I) (h : Even S.card) : subsetSign S = 1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = 1)

theorem subsetSign_of_odd (S : Finset I) (h : Odd S.card) : subsetSign S = -1 := by
  simpa only [subsetSign] using (h.neg_one_pow : (-1 : ℤ) ^ S.card = -1)

theorem subsetSign_insert [DecidableEq I] (p : I) (S : Finset I) (hp : p ∉ S) :
    subsetSign (insert p S) = -subsetSign S := by
  simp only [subsetSign, Finset.card_insert_of_notMem hp, pow_succ, mul_neg_one]

/-- The signed subset count vanishes by pairing along an actual element of `t`. -/
theorem sum_subsetSign_eq_zero (t : Finset I) (ht : t.Nonempty) :
    ∑ S ∈ t.powerset, subsetSign S = 0 := by
  classical
  obtain ⟨p, hp⟩ := ht
  have hpaired :
      (∑ S ∈ (t.erase p).powerset, subsetSign (insert p S)) =
        -(∑ S ∈ (t.erase p).powerset, subsetSign S) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    exact subsetSign_insert p S
      (fun h => (Finset.notMem_erase p t) ((Finset.mem_powerset.mp hS) h))
  calc
    _ = ∑ S ∈ (insert p (t.erase p)).powerset, subsetSign S := by
      rw [Finset.insert_erase hp]
    _ = (∑ S ∈ (t.erase p).powerset, subsetSign S) +
        ∑ S ∈ (t.erase p).powerset, subsetSign (insert p S) :=
      Finset.sum_powerset_insert (Finset.notMem_erase p t) subsetSign
    _ = 0 := by rw [hpaired, add_neg_cancel]

/-- The even-cardinality and odd-cardinality subset filters have equal size. -/
theorem card_even_subsets_eq_card_odd_subsets (t : Finset I) (ht : t.Nonempty) :
    (t.powerset.filter (fun S => Even S.card)).card =
      (t.powerset.filter (fun S => Odd S.card)).card := by
  classical
  have heven : (∑ S ∈ t.powerset.filter (fun S => Even S.card), subsetSign S) =
      ((t.powerset.filter (fun S => Even S.card)).card : ℤ) := by
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Even S.card), (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_even S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hodd : (∑ S ∈ t.powerset.filter (fun S => ¬ Even S.card), subsetSign S) =
      -((t.powerset.filter (fun S => Odd S.card)).card : ℤ) := by
    have hfilter : t.powerset.filter (fun S => ¬ Even S.card) =
        t.powerset.filter (fun S => Odd S.card) := by
      ext S
      simp only [Finset.mem_filter, Nat.not_even_iff_odd]
    rw [hfilter]
    calc
      _ = ∑ _S ∈ t.powerset.filter (fun S => Odd S.card), (-1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro S hS
        exact subsetSign_of_odd S (Finset.mem_filter.mp hS).2
      _ = _ := by simp
  have hsum := Finset.sum_filter_add_sum_filter_not t.powerset
    (fun S : Finset I => Even S.card) subsetSign
  rw [heven, hodd, sum_subsetSign_eq_zero t ht] at hsum
  exact Int.natCast_inj.mp (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum))

/-- Numerator before introducing any inverse, available in a coefficient ring. -/
def evenSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Even S.card), x S

/-- Denominator before introducing any inverse, available in a coefficient ring. -/
def oddSubsetProduct {G : Type uG} [CommMonoid G] (t : Finset I)
    (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset.filter (fun S => Odd S.card), x S

theorem map_evenSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (evenSubsetProduct t x) = evenSubsetProduct t (fun S => f (x S)) := by
  simp only [evenSubsetProduct, map_prod]

theorem map_oddSubsetProduct {G : Type uG} {H : Type uH} [CommMonoid G] [CommMonoid H]
    (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (oddSubsetProduct t x) = oddSubsetProduct t (fun S => f (x S)) := by
  simp only [oddSubsetProduct, map_prod]

section DivisionCommMonoid

variable {G : Type uG} [DivisionCommMonoid G]

/-- The alternating product of the actual family indexed by subsets of `t`. -/
def alternatingProduct (t : Finset I) (x : Finset I → G) : G :=
  ∏ S ∈ t.powerset, (x S) ^ subsetSign S

@[simp] theorem alternatingProduct_empty (x : Finset I → G) :
    alternatingProduct ∅ x = x ∅ := by
  simp [alternatingProduct]

@[simp] theorem alternatingProduct_one (t : Finset I) :
    alternatingProduct t (fun _ => (1 : G)) = 1 := by
  simp [alternatingProduct]

theorem alternatingProduct_congr (t : Finset I) (x y : Finset I → G)
    (h : ∀ S ⊆ t, x S = y S) :
    alternatingProduct t x = alternatingProduct t y := by
  apply Finset.prod_congr rfl
  intro S hS
  rw [h S (Finset.mem_powerset.mp hS)]

theorem alternatingProduct_mul (t : Finset I) (x y : Finset I → G) :
    alternatingProduct t (fun S => x S * y S) =
      alternatingProduct t x * alternatingProduct t y := by
  simp only [alternatingProduct, mul_zpow, Finset.prod_mul_distrib]

theorem alternatingProduct_inv (t : Finset I) (x : Finset I → G) :
    alternatingProduct t (fun S => (x S)⁻¹) = (alternatingProduct t x)⁻¹ := by
  simp only [alternatingProduct, inv_zpow, Finset.prod_inv_distrib]

theorem alternatingProduct_div (t : Finset I) (x y : Finset I → G) :
    alternatingProduct t (fun S => x S / y S) =
      alternatingProduct t x / alternatingProduct t y := by
  simp only [alternatingProduct, div_zpow, Finset.prod_div_distrib]

/-- A single direction pairs each omitted-`p` subset with its insertion.
The exponent at the inserted subset is the negative of the original one. -/
theorem alternatingProduct_insert [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∉ t) :
    alternatingProduct (insert p t) x =
      ∏ S ∈ t.powerset, (x S / x (insert p S)) ^ subsetSign S := by
  unfold alternatingProduct
  rw [Finset.prod_powerset_insert hp, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S hS
  have hpS : p ∉ S := fun h => hp ((Finset.mem_powerset.mp hS) h)
  rw [subsetSign_insert p S hpS, zpow_neg, div_zpow, div_eq_mul_inv]

theorem alternatingProduct_pair [DecidableEq I] (t : Finset I)
    (x : Finset I → G) (p : I) (hp : p ∈ t) :
    alternatingProduct t x =
      ∏ S ∈ (t.erase p).powerset, (x S / x (insert p S)) ^ subsetSign S := by
  calc
    alternatingProduct t x = alternatingProduct (insert p (t.erase p)) x := by
      rw [Finset.insert_erase hp]
    _ = _ := alternatingProduct_insert (t.erase p) x p (Finset.notMem_erase p t)

/-- Even subsets contribute the value itself; odd subsets contribute its inverse. -/
theorem alternatingProduct_eq_parity (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x =
      ∏ S ∈ t.powerset, if Even S.card then x S else (x S)⁻¹ := by
  classical
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp only [subsetSign_of_even S h, zpow_one, ite_eq_left h]
  · have ho : Odd S.card := Nat.not_even_iff_odd.mp h
    simp only [subsetSign_of_odd S ho, zpow_neg_one, ite_eq_right h]

/-- Collect the signed powers as a quotient of two ordinary products.
Both products themselves make sense before passing to a fraction field. -/
theorem alternatingProduct_eq_even_div_odd (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x = evenSubsetProduct t x / oddSubsetProduct t x := by
  classical
  rw [alternatingProduct_eq_parity, evenSubsetProduct, oddSubsetProduct,
    Finset.prod_filter, Finset.prod_filter, div_eq_mul_inv,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro S _
  by_cases h : Even S.card
  · simp [h, Nat.not_odd_iff_even.mpr h]
  · simp [h, Nat.not_even_iff_odd.mp h]

end DivisionCommMonoid

section CommGroup

variable {G : Type uG} {H : Type uH} [CommGroup G] [DivisionCommMonoid H]

/-- In particular this applies to the homomorphism from local units to the
fraction field, retaining the single fixed alternating product. -/
theorem map_alternatingProduct (f : G →* H) (t : Finset I) (x : Finset I → G) :
    f (alternatingProduct t x) = alternatingProduct t (fun S => f (x S)) := by
  simp only [alternatingProduct, map_prod, map_zpow]

/-- A nonempty index set cancels every constant family, by actual subset pairing. -/
theorem alternatingProduct_const (t : Finset I) (ht : t.Nonempty) (c : G) :
    alternatingProduct t (fun _ => c) = 1 := by
  classical
  obtain ⟨p, hp⟩ := ht
  rw [alternatingProduct_pair t (fun _ => c) p hp]
  simp

/-- Clearing the odd-subset denominator inside the group of units.
Mapping this equality into the fraction field gives the polynomial identity
needed before applying a homomorphism defined only on the coefficient ring. -/
theorem alternatingProduct_mul_oddSubsetProduct (t : Finset I) (x : Finset I → G) :
    alternatingProduct t x * oddSubsetProduct t x = evenSubsetProduct t x := by
  rw [alternatingProduct_eq_even_div_odd, div_mul_cancel]

end CommGroup

section FiniteUniverse

variable [Fintype I] {G : Type uG} [DivisionCommMonoid G]

/-- The full prime-index product, using all subsets of the finite index type. -/
def fullAlternatingProduct (x : Finset I → G) : G :=
  alternatingProduct Finset.univ x

theorem fullAlternatingProduct_pair [DecidableEq I] (x : Finset I → G) (p : I) :
    fullAlternatingProduct x =
      ∏ S ∈ ((Finset.univ : Finset I).erase p).powerset,
        (x S / x (insert p S)) ^ subsetSign S :=
  alternatingProduct_pair Finset.univ x p (Finset.mem_univ p)

end FiniteUniverse

theorem fullAlternatingProduct_const [Fintype I] [Nonempty I]
    {G : Type uG} [CommGroup G] (c : G) :
    fullAlternatingProduct (fun _ : Finset I => c) = 1 :=
  alternatingProduct_const Finset.univ Finset.univ_nonempty c

end CirculantHadamard

end OAI
