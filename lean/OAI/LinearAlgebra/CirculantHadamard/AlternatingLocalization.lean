import OAI.LinearAlgebra.CirculantHadamard.AlternatingProducts
import OAI.LinearAlgebra.CirculantHadamard.LocalizationIntersection
import OAI.LinearAlgebra.CirculantHadamard.LocalizationMaps
import OAI.LinearAlgebra.CirculantHadamard.ResidueOneAssociation
import OAI.LinearAlgebra.CirculantHadamard.CyclotomicAwayLocal
import OAI.LinearAlgebra.CirculantHadamard.PrimeCharacterEvaluations
import OAI.LinearAlgebra.CirculantHadamard.LocalComparison
import OAI.LinearAlgebra.CirculantHadamard.CoefficientEvaluation
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace OAI

universe uR uK uAZero uS uL uI uk

/-!
# Local representatives of the fixed alternating product

All local rings are actual localizations at maximal ideals. Their maps
into the common fraction field are canonical. The adjoined-root comparison
map is constructed from the actual base-ring inclusion and cyclotomic relation.
Membership in every maximal localization implies membership in the base ring.
-/

noncomputable section

namespace CirculantHadamard.AlternatingLocalization

open scoped BigOperators

abbrev AtMaximal (R : Type uR) [CommRing R] (m : MaximalSpectrum R) :=
  Localization.AtPrime m.asIdeal

def toFraction {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : AtMaximal R m →ₐ[R] K :=
  Localization.mapToFractionRing K m.asIdeal.primeCompl (AtMaximal R m)
    m.asIdeal.primeCompl_le_nonZeroDivisors

theorem toFraction_injective {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) : Function.Injective (toFraction K m) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := m.asIdeal.primeCompl) (AtMaximal R m) (toFraction K m).toRingHom
  intro a ha
  change toFraction K m (algebraMap R (AtMaximal R m) a) = 0 at ha
  rw [AlgHom.commutes] at ha
  have ha0 : a = 0 := IsFractionRing.injective R K (by simpa only [map_zero] using ha)
  rw [ha0, map_zero]

/-- The integral representative and a local representative of the same fixed
fraction agree under the actual coefficient localization map. -/
theorem local_representative_eq {R : Type uR} [CommRing R] [IsDomain R]
    (K : Type uK) [Field K] [Algebra R K] [IsFractionRing R K]
    (m : MaximalSpectrum R) (b : R) (v : AtMaximal R m)
    (h : algebraMap R K b = toFraction K m v) :
    algebraMap R (AtMaximal R m) b = v := by
  apply toFraction_injective K m
  simpa only [AlgHom.commutes] using h

section ActualComparisonMap

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- The actual coefficient localization at the contracted prime. Maximality
of the contraction is a separate input to the local comparison theorem, not
an assumption needed to construct this map. -/
abbrev AtComap (f : A₀ →+* R) (m : MaximalSpectrum R) :=
  Localization.AtPrime (m.asIdeal.comap f)

def baseToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) :
    AtComap f m →+* AtMaximal R m :=
  localizationAtComapMap f m.asIdeal

@[simp] theorem baseToLocal_algebraMap (f : A₀ →+* R) (m : MaximalSpectrum R)
    (a : A₀) :
    baseToLocal f m (algebraMap A₀ (AtComap f m) a) =
      algebraMap R (AtMaximal R m) (f a) :=
  localizationAtComapMap_algebraMap f m.asIdeal a

/-- The comparison algebra is mapped by the universal property of its actual
cyclotomic quotient, rather than by assuming an arbitrary extension map. -/
def comparisonToLocal (f : A₀ →+* R) (m : MaximalSpectrum R) (p : ℕ) (rho : R)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    AdjoinRoot (Polynomial.cyclotomic p (AtComap f m)) →+* AtMaximal R m :=
  AdjoinRoot.lift (baseToLocal f m) (algebraMap R (AtMaximal R m) rho) (by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic,
      Polynomial.cyclotomic.eval_apply, hroot, map_zero])

@[simp] theorem comparisonToLocal_root (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.root (Polynomial.cyclotomic p (AtComap f m))) =
      algebraMap R (AtMaximal R m) rho :=
  AdjoinRoot.lift_root _

@[simp] theorem comparisonToLocal_of (f : A₀ →+* R) (m : MaximalSpectrum R)
    (p : ℕ) (rho : R) (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (a : AtComap f m) :
    comparisonToLocal f m p rho hroot
        (AdjoinRoot.of (Polynomial.cyclotomic p (AtComap f m)) a) =
      baseToLocal f m a :=
  AdjoinRoot.lift_of _

/-- Residue characteristic is derived from membership of the rational prime,
not assumed as an independent property of the chosen maximal ideal. -/
theorem residue_charP (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) :
    CharP (IsLocalRing.ResidueField (AtMaximal R m)) p := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  have hpzero : (p : k) = 0 := by
    have hm : algebraMap R (AtMaximal R m) (p : R) ∈
        IsLocalRing.maximalIdeal (AtMaximal R m) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (AtMaximal R m) m.asIdeal _).mpr hpm
    simpa only [map_natCast] using (IsLocalRing.residue_eq_zero_iff _).mpr hm
  exact (CharP.charP_iff_prime_eq_zero hp).mpr hpzero

/-- A p-th root has residue one at every maximal ideal containing p. -/
theorem residue_root_eq_one (m : MaximalSpectrum R) (p : ℕ) (hp : p.Prime)
    (hpm : (p : R) ∈ m.asIdeal) (rho : R) (hrho : rho ^ p = 1) :
    IsLocalRing.residue (AtMaximal R m) (algebraMap R (AtMaximal R m) rho) = 1 := by
  let k := IsLocalRing.ResidueField (AtMaximal R m)
  let : Fact p.Prime := ⟨hp⟩
  let : CharP k p := residue_charP m p hp hpm
  let r : k := IsLocalRing.residue (AtMaximal R m)
    (algebraMap R (AtMaximal R m) rho)
  have hpow : r ^ p = 1 := by
    dsimp [r]
    rw [← map_pow, ← map_pow, hrho, map_one, map_one]
  have hnil : (r - 1) ^ p = 0 := by rw [sub_pow_char, hpow, one_pow, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hnil)

theorem residue_unit_eq_one_of_span {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing L] (f : S →+* L) (rho : S) (v : Sˣ)
    (hv : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) :
    IsLocalRing.residue L ((Units.map f.toMonoidHom v : Lˣ) : L) = 1 := by
  let g : S →+* IsLocalRing.ResidueField L := (IsLocalRing.residue L).comp f
  have hspan : Ideal.span ({rho - 1} : Set S) ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = rho - 1 := Set.mem_singleton_iff.mp ha
    subst a
    change g (rho - 1) = 0
    simp only [map_sub, map_one, RingHom.comp_apply, g, hrho, sub_self]
  have hz := hspan hv
  change g ((v : S) - 1) = 0 at hz
  have hval : g (v : S) = 1 := sub_eq_zero.mp (by simpa only [map_sub, map_one] using hz)
  exact hval

theorem map_residueOneAssociated {S : Type uS} {L : Type uL} [CommRing S] [CommRing L]
    [IsLocalRing S] [IsLocalRing L] (f : S →+* L) (rho : S)
    (hmax : IsLocalRing.maximalIdeal S = Ideal.span ({rho - 1} : Set S))
    (hrho : IsLocalRing.residue L (f rho) = 1) {a b : S}
    (hab : LocalComparison.ResidueOneAssociated (IsLocalRing.residue S) a b) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue L) (f a) (f b) := by
  obtain ⟨v, hv, hres⟩ := hab
  have hspan : (v : S) - 1 ∈ Ideal.span ({rho - 1} : Set S) := by
    rw [← hmax]
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [map_sub, map_one, hres, sub_self]
  refine ⟨Units.map f.toMonoidHom v, ?_,
    residue_unit_eq_one_of_span f rho v hspan hrho⟩
  change f a = f (v : S) * f b
  simpa only [map_mul, Units.coe_map] using congrArg f hv

end ActualComparisonMap

/-- The local association is converted to the actual fraction-field quotient
only after the augmentation image is known to be nonzero. -/
theorem local_edge_of_associated {R : Type uR} {K : Type uK} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] (m : MaximalSpectrum R)
    (a b : R) (hb : algebraMap R K b ≠ 0)
    (h : LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m) a) (algebraMap R (AtMaximal R m) b)) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) = algebraMap R K a / algebraMap R K b ∧
      IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1 := by
  obtain ⟨v, hv, hres⟩ := h
  refine ⟨v, ?_, hres⟩
  apply (eq_div_iff hb).mpr
  have hmap := congrArg (toFraction K m) hv
  simpa only [map_mul, AlgHom.commutes] using hmap.symm

/-- A finite prime factorization supplies the away-from-u unit, including u=1. -/
theorem natCast_isUnit_of_primeFactors {R : Type uR} [CommRing R]
    (u : ℕ) (hu : u ≠ 0) (hprime : ∀ p ∈ u.primeFactors, IsUnit (p : R)) :
    IsUnit (u : R) := by
  rw [← Nat.prod_primeFactorsList hu, Nat.cast_list_prod]
  apply List.prod_isUnit
  intro a ha
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact hprime p (Nat.mem_primeFactors_iff_mem_primeFactorsList.mpr hp)

theorem local_norm_factor_isUnit {R : Type uR} [CommRing R]
    (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal)
    (x y : R) (hnorm : x * y = (u : R) ^ 2) :
    IsUnit (algebraMap R (AtMaximal R m) x) := by
  have huunit : IsUnit (u : AtMaximal R m) :=
    natCast_isUnit_of_primeFactors u hu (fun p hp => by
      have h := (IsLocalization.AtPrime.isUnit_to_map_iff
        (AtMaximal R m) m.asIdeal (p : R)).mpr (havoid p hp)
      simpa only [map_natCast] using h)
  apply isUnit_of_mul_isUnit_left (y := algebraMap R (AtMaximal R m) y)
  rw [← map_mul, hnorm, map_pow, map_natCast]
  exact huunit.pow 2

section AlternatingUnits

variable {I : Type uI} {R : Type uR} {K : Type uK} {k : Type uk} [DecidableEq I] [CommRing R] [Field K] [Field k]

theorem exists_unit_of_edges (f : R →+* K) (res : R →+* k)
    (t : Finset I) (p : I) (hp : p ∈ t) (x : Finset I → K)
    (hedge : ∀ S ∈ (t.erase p).powerset, ∃ v : Rˣ,
      f (v : R) = x (insert p S) / x S ∧ res (v : R) = 1) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t x ∧ res (v : R) = 1 := by
  classical
  let edge : Finset I → Rˣ := fun S =>
    if hS : S ∈ (t.erase p).powerset then Classical.choose (hedge S hS) else 1
  have hedge' : ∀ S ∈ (t.erase p).powerset,
      f (edge S : R) = x (insert p S) / x S ∧ res (edge S : R) = 1 := by
    intro S hS
    simpa only [edge, dite_eq_left hS] using Classical.choose_spec (hedge S hS)
  let v : Rˣ := ∏ S ∈ (t.erase p).powerset, (edge S)⁻¹ ^ subsetSign S
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  let tok : Rˣ →* k := res.toMonoidHom.comp (Units.coeHom R)
  refine ⟨v, ?_, ?_⟩
  · change toK v = alternatingProduct t x
    rw [alternatingProduct_pair t x p hp]
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_congr rfl
    intro S hS
    change (f (edge S : R))⁻¹ ^ subsetSign S = _
    rw [(hedge' S hS).1, inv_div]
  · change tok v = 1
    simp only [v, map_prod, map_zpow, map_inv]
    apply Finset.prod_eq_one
    intro S hS
    change (res (edge S : R))⁻¹ ^ subsetSign S = 1
    rw [(hedge' S hS).2, inv_one, one_zpow]

/-- Ordinary local units give an actual local unit representative of the fixed
field product. The representatives are not independently chosen field values. -/
theorem exists_unit_of_factor_units (f : R →+* K) (t : Finset I)
    (x : Finset I → R) (hx : ∀ S ⊆ t, IsUnit (x S)) :
    ∃ v : Rˣ, f (v : R) = alternatingProduct t (fun S => f (x S)) := by
  classical
  let units : Finset I → Rˣ := fun S => if hS : S ⊆ t then (hx S hS).unit else 1
  have hval : ∀ S ⊆ t, (units S : R) = x S := by
    intro S hS
    simp only [units, dite_eq_left hS, IsUnit.unit_spec]
  let toK : Rˣ →* K := f.toMonoidHom.comp (Units.coeHom R)
  refine ⟨alternatingProduct t units, ?_⟩
  change toK (alternatingProduct t units) = _
  rw [map_alternatingProduct]
  apply alternatingProduct_congr
  intro S hS
  change f (units S : R) = f (x S)
  rw [hval S hS]

end AlternatingUnits

section MaximalCover

variable {I : Type uI} {R : Type uR} {K : Type uK} [DecidableEq I] [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The away-from-u case uses only the evaluated norm identity and avoidance
of the actual rational prime factors of u. -/
theorem exists_local_unit_away (m : MaximalSpectrum R) (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (x y : Finset I → R)
    (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal) :
    ∃ v : (AtMaximal R m)ˣ,
      toFraction K m (v : AtMaximal R m) =
        alternatingProduct t (fun S => algebraMap R K (x S)) := by
  obtain ⟨v, hv⟩ := exists_unit_of_factor_units (toFraction K m).toRingHom t
    (fun S => algebraMap R (AtMaximal R m) (x S))
    (fun S hS => local_norm_factor_isUnit m u hu havoid (x S) (y S) (hnorm S hS))
  refine ⟨v, ?_⟩
  change toFraction K m (v : AtMaximal R m) = alternatingProduct t
    (fun S => toFraction K m (algebraMap R (AtMaximal R m) (x S))) at hv
  simpa only [AlgHom.commutes] using hv

/-- Every maximal ideal is covered either by a genuine prime-direction edge
comparison or by the norm argument. Local character comparison supplies the
edge hypotheses, without assuming that the product belongs to the base ring. -/
theorem exists_base_of_edges_and_norm (u : ℕ) (hu : u ≠ 0)
    (t : Finset I) (prime : I → ℕ)
    (hcover : ∀ p ∈ u.primeFactors, ∃ i ∈ t, prime i = p)
    (x y : Finset I → R) (hnorm : ∀ S ⊆ t, x S * y S = (u : R) ^ 2)
    (hedge : ∀ m : MaximalSpectrum R, ∀ i ∈ t, (prime i : R) ∈ m.asIdeal →
      ∀ S ∈ (t.erase i).powerset, ∃ v : (AtMaximal R m)ˣ,
        toFraction K m (v : AtMaximal R m) =
          algebraMap R K (x (insert i S)) / algebraMap R K (x S) ∧
        IsLocalRing.residue (AtMaximal R m) (v : AtMaximal R m) = 1) :
    ∃ b : R, algebraMap R K b =
      alternatingProduct t (fun S => algebraMap R K (x S)) := by
  classical
  apply exists_base_of_localization_images
  intro m
  by_cases hm : ∃ p ∈ u.primeFactors, (p : R) ∈ m.asIdeal
  · obtain ⟨p, hp, hpm⟩ := hm
    obtain ⟨i, hi, hpi⟩ := hcover p hp
    have him : (prime i : R) ∈ m.asIdeal := by rw [hpi]; exact hpm
    obtain ⟨v, hv, _⟩ := exists_unit_of_edges (toFraction K m).toRingHom
      (IsLocalRing.residue (AtMaximal R m)) t i hi
      (fun S => algebraMap R K (x S)) (hedge m i hi him)
    exact ⟨v, hv⟩
  · have havoid : ∀ p ∈ u.primeFactors, (p : R) ∉ m.asIdeal := by
      intro p hp hpm
      exact hm ⟨p, hp, hpm⟩
    obtain ⟨v, hv⟩ := exists_local_unit_away (K := K) m u hu t x y hnorm havoid
    exact ⟨v, hv⟩

end MaximalCover

section ConcreteComparison

open CyclicRing

/-- Bezout makes the complementary integer factor a unit in the actual
localization at any prime containing `p`. -/
theorem coprime_natCast_isUnit {R : Type uR} [CommRing R]
    (I : Ideal R) [I.IsPrime] (p c : ℕ) (hpc : Nat.Coprime p c)
    (hpI : (p : R) ∈ I) : IsUnit (c : Localization.AtPrime I) := by
  have hcI : (c : R) ∉ I := by
    intro hc
    obtain ⟨a, b, hab⟩ := hpc.cast (R := R)
    have hone : (1 : R) ∈ I := by
      rw [← hab]
      exact I.add_mem (I.mul_mem_left a hpI) (I.mul_mem_left b hc)
    exact (inferInstance : I.IsPrime).ne_top (I.eq_top_iff_one.mpr hone)
  simpa only [map_natCast] using
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime I) I (c : R)).mpr hcI

variable {A₀ : Type uAZero} {R : Type uR} [CommRing A₀] [CommRing R]

/-- Apply the proved DVR comparison after coefficient localization and map its
actual unit through the cyclotomic quotient into the target maximal localization.
The group order and scalar prime exponent are the same `p ^ (e + 1)`. -/
theorem actual_local_character_association
    (f : A₀ →+* R) (m : MaximalSpectrum R)
    [IsDomain (AtComap f m)] [CharZero (AtComap f m)]
    [IsDiscreteValuationRing (AtComap f m)]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpm : (p : R) ∈ m.asIdeal)
    (hmax : IsLocalRing.maximalIdeal (AtComap f m) =
      Ideal.span {(p : AtComap f m)})
    (rho : R) (hrho : rho ^ p = 1)
    (hroot : (Polynomial.cyclotomic p R).eval rho = 0)
    (n e c : ℕ) [NeZero n] (hn : n = p ^ (e + 1))
    (hrhon : rho ^ n = 1) (hc : IsUnit (c : AtComap f m))
    (F K : Elem A₀ n)
    (hFK : F * K = scalar n ((p : A₀) ^ (e + 1) * (c : A₀))) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal R m))
      (algebraMap R (AtMaximal R m)
        (evaluate f (CyclicPolynomial.powerCharacter n rho hrhon) F))
      (algebraMap R (AtMaximal R m) (evaluate f 1 F)) := by
  subst n
  let A := AtComap f m
  let L := AtMaximal R m
  let φ : A₀ →+* A := algebraMap A₀ A
  let FA := coefficientMap φ (p ^ (e + 1)) F
  let KA := coefficientMap φ (p ^ (e + 1)) K
  have hFA : FA * KA = scalar (p ^ (e + 1))
      ((p : A) ^ (e + 1) * (hc.unit : A)) := by
    dsimp [FA, KA]
    rw [← map_mul, hFK, coefficientMap_scalar, map_mul, map_pow,
      map_natCast, map_natCast]
  obtain ⟨v, hv, hvspan⟩ :=
    (LocalComparison.local_character_comparison A p hp hmax e hc.unit FA KA hFA).1
  let j : RamifiedLocal.Extension A p 0 →+* L :=
    comparisonToLocal f m (p ^ (0 + 1)) rho (by simpa only [Nat.zero_add, pow_one] using hroot)
  have jroot : j (LocalComparison.orderPRoot A p) = algebraMap R L rho := by
    exact comparisonToLocal_root f m _ rho _
  have jcoeff (a : A) : j (algebraMap A (RamifiedLocal.Extension A p 0) a) =
      baseToLocal f m a := by
    exact comparisonToLocal_of f m _ rho _ a
  have evalRoot :
      (j.comp (LocalComparison.orderPValue A p e).toRingHom).comp
          (coefficientMap φ (p ^ (e + 1))) =
        (algebraMap R L).comp
          (evaluate f (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro r
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single 0 r))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single 0 r))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ (0 : ZMod (p ^ (e + 1))).val)
        (baseToLocal_algebraMap f m r)
    · intro a
      change j (evaluateAt (p ^ (e + 1)) (LocalComparison.orderPRoot A p)
          (LocalComparison.orderPRoot_pow_level A p e)
          (coefficientMap φ (p ^ (e + 1)) (AddMonoidAlgebra.single a 1))) =
        algebraMap R L (evaluate f
          (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon)
          (AddMonoidAlgebra.single a 1))
      simp only [coefficientMap_single, evaluateAt_single, evaluate_single,
        CyclicPolynomial.powerCharacter_apply, map_mul, map_pow, jroot,
        jcoeff, φ]
      exact congrArg (fun z : L => z * (algebraMap R L rho) ^ a.val)
        (baseToLocal_algebraMap f m (1 : A₀))
  have evalOne : j (algebraMap A (RamifiedLocal.Extension A p 0)
      (augmentation (p ^ (e + 1)) FA)) =
        algebraMap R L (evaluate f 1 F) := by
    rw [jcoeff]
    dsimp [FA]
    rw [augmentation_coefficientMap, baseToLocal_algebraMap,
      evaluate_trivial_eq_augmentation]
  have hres : IsLocalRing.residue L
      ((Units.map j.toMonoidHom v : Lˣ) : L) = 1 := by
    apply residue_unit_eq_one_of_span j (LocalComparison.orderPRoot A p) v
    · exact hvspan
    · rw [jroot]
      exact residue_root_eq_one m p hp hpm rho hrho
  refine ⟨Units.map j.toMonoidHom v, ?_, hres⟩
  have heval := DFunLike.congr_fun evalRoot F
  change j (LocalComparison.orderPValue A p e FA) =
    algebraMap R L (evaluate f
      (CyclicPolynomial.powerCharacter (p ^ (e + 1)) rho hrhon) F) at heval
  rw [← heval]
  change j (LocalComparison.orderPValue A p e FA) =
    j (v : RamifiedLocal.Extension A p 0) * algebraMap R L (evaluate f 1 F)
  simpa only [map_mul, evalOne, Units.coe_map] using congrArg j hv

end ConcreteComparison

section ActualAlternatingProduct

open CyclotomicRings PrimeComponents PrimeCharacterEvaluations CyclicRing

/-- Name the canonical algebra structures directly to avoid searching through
iterated-localization algebra instances for the concrete coefficient ring. -/
instance B_local_algebra (u : ℕ) (m : MaximalSpectrum (B u)) :
    Algebra (B u) (AtMaximal (B u) m) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := m.asIdeal.primeCompl)

instance B_fraction_algebra (u : ℕ) : Algebra (B u) (FractionRing (B u)) :=
  OreLocalization.instAlgebra (R := B u) (R₀ := B u) (S := nonZeroDivisors (B u))

/-- The selected element of B satisfies the actual cyclotomic relation. -/
theorem rhoB_cyclotomic_root (u : ℕ) (p : PrimeIndex u) :
    (Polynomial.cyclotomic p.val (B u)).eval (rhoB u p) = 0 := by
  have hp := prime_of_mem p.property
  apply Subtype.val_injective
  change (B u).val ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) =
    (B u).val (0 : B u)
  rw [map_zero]
  change (B u).val.toRingHom
    ((Polynomial.cyclotomic p.val (B u)).eval (rhoB u p)) = 0
  rw [← Polynomial.cyclotomic.eval_apply]
  exact (rho_isPrimitiveRoot p.val hp.ne_zero).isRoot_cyclotomic hp.pos

theorem subset_evaluations_local_associated (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    LocalComparison.ResidueOneAssociated (IsLocalRing.residue (AtMaximal (B u) m))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu (insert p S) x))
      (algebraMap (B u) (AtMaximal (B u) m) (subsetEvaluation u hu S x)) := by
  let f := (awayInclusion u p.val).toRingHom
  let A := AtComap f m
  let : NeZero p.val := ⟨(prime_of_mem p.property).ne_zero⟩
  let : CharZero A := CyclotomicAwayLocal.awayLocal_charZero u p.val m.asIdeal
  let : IsDiscreteValuationRing A :=
    CyclotomicAwayLocal.awayLocal_isDiscreteValuationRing u p.val huodd p.property m.asIdeal hpm
  have hmax : IsLocalRing.maximalIdeal A = Ideal.span {(p.val : A)} :=
    CyclotomicAwayLocal.awayLocal_maximalIdeal_eq_span u p.val huodd p.property m.asIdeal hpm
  let e := exponent u p.val - 1
  have he : exponent u p.val = e + 1 := by
    dsimp [e]
    have hpos := exponent_pos hu p.property
    omega
  have hn : order u p.val = p.val ^ (e + 1) := by rw [order, he]
  have hc : IsUnit (cofactor u p.val : A) :=
    coprime_natCast_isUnit (m.asIdeal.comap f) p.val (cofactor u p.val)
      (cofactor_coprime hu p.property)
      (CyclotomicAwayLocal.prime_mem_awayPrime u p.val m.asIdeal hpm)
  let F := partialEvaluation u hu p S x
  let K := partialEvaluation u hu p S (ringStar x)
  have hnum : u ^ 2 = p.val ^ (e + 1) * cofactor u p.val := by
    rw [← hn]
    exact (order_mul_cofactor u p.val).symm
  have hFK : F * K = scalar (order u p.val)
      ((p.val : awayRing u p.val) ^ (e + 1) * (cofactor u p.val : awayRing u p.val)) := by
    dsimp [F, K]
    rw [partialEvaluation_product u hu p S x (ringStar x) hx]
    apply congrArg (scalar (order u p.val))
    exact_mod_cast hnum
  have h := actual_local_character_association f m p.val (prime_of_mem p.property)
    hpm hmax (rhoB u p) (rhoB_pow u p) (rhoB_cyclotomic_root u p)
    (order u p.val) e (cofactor u p.val) hn
    (root_order_pow u hu p (rhoB u p) (rhoB_pow u p)) hc F K hFK
  change LocalComparison.ResidueOneAssociated _
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtRoot u hu p F))
    (algebraMap (B u) (AtMaximal (B u) m) (partialAtOne u p F)) at h
  simpa only [F, partialEvaluation_at_root_apply,
    partialEvaluation_at_one_apply u hu p S hpS x] using h

/-- The denominator is nonzero because it is an actual evaluated norm factor. -/
theorem exists_local_edge_unit (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal)
    (S : Finset (PrimeIndex u)) (hpS : p ∉ S) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu (insert p S) x) /
          algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  apply local_edge_of_associated m _ _
  · intro hz
    apply subsetEvaluation_ne_zero u hu S x hx
    apply IsFractionRing.injective (B u) (FractionRing (B u))
    simpa only [map_zero] using hz
  · exact subset_evaluations_local_associated u hu huodd x hx p m hpm S hpS

/-- At every maximal ideal over p, the one fixed global alternating product
is the image of a unit with residue one. No edge comparison is an input. -/
theorem exists_local_unit_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing))
    (p : PrimeIndex u) (m : MaximalSpectrum (B u))
    (hpm : (p.val : B u) ∈ m.asIdeal) :
    ∃ v : (AtMaximal (B u) m)ˣ,
      toFraction (FractionRing (B u)) m (v : AtMaximal (B u) m) =
        alternatingProduct (Finset.univ : Finset (PrimeIndex u))
          (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) ∧
      IsLocalRing.residue (AtMaximal (B u) m) (v : AtMaximal (B u) m) = 1 := by
  classical
  apply exists_unit_of_edges (toFraction (FractionRing (B u)) m).toRingHom
    (IsLocalRing.residue (AtMaximal (B u) m)) Finset.univ p (Finset.mem_univ p)
  intro S hS
  have hpS : p ∉ S := fun hp =>
    (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
  exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

/-- Integrality of the actual subset-character alternating product. The
maximal ideals over prime divisors use the proved local comparison; every
other maximal ideal uses the actual norm identity. -/
theorem exists_integral_alternatingProduct (u : ℕ) [NeZero (u ^ 2)]
    (hu : 0 < u) (huodd : Odd u)
    (x : Elem GaussianRing (u ^ 2))
    (hx : x * ringStar x = scalar (u ^ 2) ((u ^ 2 : ℕ) : GaussianRing)) :
    ∃ z : B u, algebraMap (B u) (FractionRing (B u)) z =
      alternatingProduct (Finset.univ : Finset (PrimeIndex u))
        (fun S => algebraMap (B u) (FractionRing (B u)) (subsetEvaluation u hu S x)) := by
  classical
  refine exists_base_of_edges_and_norm u hu.ne' Finset.univ
    (fun p : PrimeIndex u => p.val) ?_
    (fun S => subsetEvaluation u hu S x) (fun S => star (subsetEvaluation u hu S x)) ?_ ?_
  · intro p hp
    exact ⟨⟨p, hp⟩, Finset.mem_univ _, rfl⟩
  · intro S _
    simpa only [Nat.cast_pow] using subsetEvaluation_norm u hu S x hx
  · intro m p _ hpm S hS
    have hpS : p ∉ S := fun hp =>
      (Finset.mem_erase.mp ((Finset.mem_powerset.mp hS) hp)).1 rfl
    exact exists_local_edge_unit u hu huodd x hx p m hpm S hpS

end ActualAlternatingProduct

end CirculantHadamard.AlternatingLocalization

end

end OAI
