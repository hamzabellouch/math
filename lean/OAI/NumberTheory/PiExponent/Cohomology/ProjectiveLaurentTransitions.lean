import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveLaurentTransitions
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {ι R : Type*} [Fintype ι] [CommRing R]

def standardExponent (i : ι) (d : ℤ) : ι → ℤ := fun k => if k = i then d else 0

omit [Fintype ι] in
@[simp] theorem standardExponent_self (i : ι) (d : ℤ) : standardExponent i d i = d := by
  simp [standardExponent]

omit [Fintype ι] in
@[simp] theorem standardExponent_other (i k : ι) (d : ℤ) (hk : k ≠ i) :
    standardExponent i d k = 0 := by simp [standardExponent, hk]

def zeroDegreeExponent (i : ι) : ({j : ι // j ≠ i} → ℤ) →+ (ι → ℤ) where
  toFun b := (fullEncode i 0 b).val
  map_zero' := by
    funext k
    by_cases hk : k = i
    · subst k; simp
    · exact fullEncode_other i 0 0 ⟨k, hk⟩
  map_add' a b := by
    funext k
    by_cases hk : k = i
    · subst k; simp [fullEncode_self, Finset.sum_add_distrib, add_comm]
    · change (fullEncode i 0 (a + b)).val (⟨k, hk⟩ : {j : ι // j ≠ i}) = _
      rw [fullEncode_other i 0 (a + b) ⟨k, hk⟩]
      change a ⟨k, hk⟩ + b ⟨k, hk⟩ = (fullEncode i 0 a).val k + (fullEncode i 0 b).val k
      rw [show (fullEncode i 0 a).val k = a ⟨k, hk⟩ from fullEncode_other i 0 a ⟨k, hk⟩,
        show (fullEncode i 0 b).val k = b ⟨k, hk⟩ from fullEncode_other i 0 b ⟨k, hk⟩]

theorem zeroDegreeExponent_injective (i : ι) : Function.Injective (zeroDegreeExponent i) := by
  intro a b h
  funext j
  have hj := congrFun h j.val
  simpa only [zeroDegreeExponent, AddMonoidHom.coe_mk, ZeroHom.coe_mk, fullEncode_other] using hj

theorem fullEncode_eq_standard_add (i : ι) (d : ℤ)
    (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val = standardExponent i d + zeroDegreeExponent i b := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, sub_eq_add_neg]
  · simp only [Pi.add_apply, standardExponent_other i k d hk, zero_add]
    exact (fullEncode_other i d b ⟨k, hk⟩).trans (fullEncode_other i 0 b ⟨k, hk⟩).symm

theorem zeroDegreeExponent_coordinate (i : ι) (j : {j : ι // j ≠ i}) :
    zeroDegreeExponent i (natExponentHom i (Finsupp.single j 1)) =
      standardExponent j.val 1 - standardExponent i 1 := by
  classical
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, fullEncode_self, natExponentHom, standardExponent,
      Ne.symm j.property, Finsupp.single_apply]
  · change (fullEncode i 0 _).val k = _
    rw [show (fullEncode i 0 _).val k =
      natExponentHom i (Finsupp.single j 1) ⟨k, hk⟩ from fullEncode_other i 0 _ ⟨k, hk⟩]
    simp [natExponentHom, standardExponent, hk, Finsupp.single_apply, Subtype.ext_iff, eq_comm]

abbrev FullGroupAlgebra := AddMonoidAlgebra R (ι → ℤ)

def chartToFull (i : ι) : chartGroupAlgebra (R := R) i →+* FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R (zeroDegreeExponent i)

theorem chartToFull_injective (i : ι) : Function.Injective (chartToFull (R := R) i) :=
  AddMonoidAlgebra.mapDomain_injective (zeroDegreeExponent_injective i)

def laurentToFull (d : ℤ) : Laurent ι R d →+ FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    (Finsupp.mapDomain.addMonoidHom (fun a : Monomial ι d => a.val))

theorem laurentToFull_injective (d : ℤ) : Function.Injective (laurentToFull (ι := ι) (R := R) d) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.injective.comp
    (Finsupp.mapDomain_injective Subtype.val_injective)

@[simp] theorem laurentToFull_single (d : ℤ) (a : Monomial ι d) (r : R) :
    laurentToFull d (Finsupp.single a r) = AddMonoidAlgebra.single a.val r := by
  simp [laurentToFull]

theorem laurentToFull_groupAlgebraToLaurent (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) :
    laurentToFull d (groupAlgebraToLaurent i d p) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * chartToFull i p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | single a r =>
      change laurentToFull d (Finsupp.domCongr (fullExponentEquiv i d) (Finsupp.single a r)) = _
      simp [chartToFull, laurentToFull_single,
        fullExponentEquiv, AddMonoidAlgebra.single_mul_single]
      exact congrArg (fun exponent => AddMonoidAlgebra.single exponent r)
        (fullEncode_eq_standard_add i d a)

def overlapToFull (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* FullGroupAlgebra (ι := ι) (R := R) :=
  (chartToFull i).comp (overlapToGroupAlgebra i s)

theorem overlapToFull_injective (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapToFull (R := R) i s) :=
  (chartToFull_injective i).comp (overlapToGroupAlgebra_injective i s)

@[simp] theorem laurentToFull_overlapLaurent (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (z : Localization.Away (chartProduct (R := R) i s)) :
    laurentToFull d (overlapLaurent i d s z) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * overlapToFull i s z :=
  laurentToFull_groupAlgebraToLaurent i d _

@[simp] theorem overlapToFull_X (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.X (R := R) k)) =
      AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1 := by
  simp [overlapToFull, chartToFull, zeroDegreeExponent_coordinate]

@[simp] theorem overlapToFull_C (i : ι) (s : Finset {j : ι // j ≠ i}) (r : R) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.C (σ := {j : ι // j ≠ i}) r)) =
      AddMonoidAlgebra.single 0 r := by
  simp only [overlapToFull, RingHom.comp_apply, overlapToGroupAlgebra_base]
  change AddMonoidAlgebra.mapDomain (zeroDegreeExponent i)
    (AddMonoidAlgebra.mapDomain (natExponentHom i) (AddMonoidAlgebra.single 0 r)) = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single]
  simp only [map_zero]

theorem overlapToFull_natural_of_generators (i j : ι)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hC : ∀ r : R, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.C (σ := {k : ι // k ≠ i}) r))) =
        AddMonoidAlgebra.single 0 r)
    (hX : ∀ k : {k : ι // k ≠ i}, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.X (R := R) k))) =
        AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1) :
    (overlapToFull j t).comp f = overlapToFull i s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct (R := R) i s))
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, overlapToFull_C] using hC r
  · intro k
    simpa only [RingHom.comp_apply, overlapToFull_X] using hX k

theorem overlapLaurent_change_pivot (i j : ι) (d : ℤ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : Localization.Away (chartProduct (R := R) j t))
    (hu : overlapToFull j t u =
      AddMonoidAlgebra.single (standardExponent i d - standardExponent j d) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j d t (u * f z) = overlapLaurent i d s z := by
  apply laurentToFull_injective d
  rw [laurentToFull_overlapLaurent, laurentToFull_overlapLaurent, map_mul, hu, ← mul_assoc,
    AddMonoidAlgebra.single_mul_single]
  have he : standardExponent j d + (standardExponent i d - standardExponent j d) =
      standardExponent i d := by abel
  rw [he, one_mul]
  have hz := RingHom.congr_fun hf z
  change overlapToFull j t (f z) = overlapToFull i s z at hz
  rw [hz]

theorem overlapLaurent_change_pivot_pow (i j : ι) (n : ℕ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : Localization.Away (chartProduct (R := R) j t))
    (hu : overlapToFull j t u =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j (n : ℤ) t (u ^ n * f z) = overlapLaurent i (n : ℤ) s z := by
  apply overlapLaurent_change_pivot i j (n : ℤ) s t f hf (u ^ n) _ z
  rw [map_pow, hu, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  funext k
  simp [standardExponent, mul_sub]

def fullMonomialUnit (a : ι → ℤ) : (FullGroupAlgebra (ι := ι) (R := R))ˣ where
  val := AddMonoidAlgebra.single a 1
  inv := AddMonoidAlgebra.single (-a) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp only [add_neg_cancel, one_mul]; rfl
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp only [neg_add_cancel, one_mul]; rfl

def fullMonomialUnits : Multiplicative (ι → ℤ) →* (FullGroupAlgebra (ι := ι) (R := R))ˣ where
  toFun a := fullMonomialUnit a.toAdd
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by
    apply Units.ext
    change AddMonoidAlgebra.single (a.toAdd + b.toAdd) 1 =
      AddMonoidAlgebra.single a.toAdd 1 * AddMonoidAlgebra.single b.toAdd 1
    rw [AddMonoidAlgebra.single_mul_single, one_mul]

omit [Fintype ι] in

theorem fullMonomialUnit_zpow (a : ι → ℤ) (d : ℤ) :
    fullMonomialUnit (R := R) (d • a) = (fullMonomialUnit a) ^ d := by
  have h := map_zpow (fullMonomialUnits (ι := ι) (R := R)) (Multiplicative.ofAdd a) d
  exact h

theorem map_coordinate_unit_zpow (j : ι) (t : Finset {k : ι // k ≠ j})
    (u : (Localization.Away (chartProduct (R := R) j t))ˣ) (a : ι → ℤ)
    (hu : overlapToFull j t (u : Localization.Away (chartProduct (R := R) j t)) =
      AddMonoidAlgebra.single a 1) (d : ℤ) :
    overlapToFull j t (↑(u ^ d) : Localization.Away (chartProduct (R := R) j t)) =
      AddMonoidAlgebra.single (d • a) 1 := by
  have h : Units.map (overlapToFull j t).toMonoidHom u = fullMonomialUnit a :=
    Units.ext hu
  calc
    _ = ↑((Units.map (overlapToFull j t).toMonoidHom u) ^ d) := by
      exact congrArg
        (fun v : (FullGroupAlgebra (ι := ι) (R := R))ˣ =>
          (v : FullGroupAlgebra (ι := ι) (R := R)))
        (map_zpow (Units.map (overlapToFull j t).toMonoidHom) u d)
    _ = ↑((fullMonomialUnit (R := R) a) ^ d) := by rw [h]
    _ = _ := by rw [← fullMonomialUnit_zpow]; rfl

theorem overlapLaurent_change_pivot_zpow (i j : ι) (d : ℤ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : (Localization.Away (chartProduct (R := R) j t))ˣ)
    (hu : overlapToFull j t (u : Localization.Away (chartProduct (R := R) j t)) =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j d t ((↑(u ^ d) : Localization.Away (chartProduct (R := R) j t)) * f z) = overlapLaurent i d s z := by
  apply overlapLaurent_change_pivot i j d s t f hf
    (↑(u ^ d) : Localization.Away (chartProduct (R := R) j t)) _ z
  rw [map_coordinate_unit_zpow j t u _ hu d]
  congr 1
  funext k
  simp [standardExponent, mul_sub]

theorem overlapToFull_ratio (i j k : ι) (t : Finset {l : ι // l ≠ j})
    (x y yinv : Localization.Away (chartProduct (R := R) j t))
    (hx : overlapToFull j t x =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent j 1) 1)
    (hy : overlapToFull j t y =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (hinv : y * yinv = 1) :
    overlapToFull j t (x * yinv) =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent i 1) 1 := by
  have hcancel := congrArg (overlapToFull j t) hinv
  rw [map_mul, hy, map_one] at hcancel
  have hunit : IsUnit (AddMonoidAlgebra.single
      (standardExponent i 1 - standardExponent j 1) (1 : R)) :=
    (fullMonomialUnit (R := R) (standardExponent i 1 - standardExponent j 1)).isUnit
  have hi : overlapToFull j t yinv = AddMonoidAlgebra.single
      (standardExponent j 1 - standardExponent i 1) 1 := by
    apply hunit.mul_left_cancel
    rw [hcancel, AddMonoidAlgebra.single_mul_single]
    have he : standardExponent i 1 - standardExponent j 1 +
        (standardExponent j 1 - standardExponent i 1) = 0 := by abel
    rw [he, one_mul]
    rfl
  rw [map_mul, hx, hi, AddMonoidAlgebra.single_mul_single]
  have he : standardExponent k 1 - standardExponent j 1 +
      (standardExponent j 1 - standardExponent i 1) =
      standardExponent k 1 - standardExponent i 1 := by abel
  rw [he, one_mul]

end
end PiExponent.GeometrySupport.ProjectiveLaurentTransitions

end OAI
