import Mathlib

namespace OAI


/-! Étale algebras obtained by adjoining roots of units, and normalization
charts for the complete-quadrangle Kummer cover in OpenAI's
*A Complete Local Domain without a Small Cohen–Macaulay Module*, Section 6. -/
noncomputable section
open Polynomial
namespace KummerEtale
variable {R : Type*} [CommRing R]

/-- A standard etale equation with localization polynomial one is precisely
its ordinary root algebra. -/
def standardPairRootEquiv (P : StandardEtalePair R) (hg : P.g = 1) :
    P.Ring ≃ₐ[R] AdjoinRoot P.f := by
  let hroot : P.HasMap (AdjoinRoot.root P.f) :=
    ⟨AdjoinRoot.eval₂_root P.f, by simp [hg]⟩
  let f := P.lift (AdjoinRoot.root P.f) hroot
  let g := AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  have hf : f P.X = AdjoinRoot.root P.f := P.lift_X _ hroot
  have hg : g (AdjoinRoot.root P.f) = P.X :=
    AdjoinRoot.liftAlgHom_root P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1
  exact AlgEquiv.ofAlgHom f g
    (by apply AdjoinRoot.algHom_ext; exact (congrArg f hg).trans hf)
    (by apply StandardEtalePair.hom_ext; exact (congrArg g hf).trans hg)

/-- Bezout identity for the unit-root equation, with the precise ring units
that make its derivative invertible. -/
lemma unitRoot_bezout (n : ℕ) (hn : 0 < n) (u v : Rˣ) (hv : (v : R) = (n : R)) :
    derivative (X ^ n - C (u : R)) * (C ((v⁻¹ * u⁻¹ : Rˣ) : R) * X) +
      (X ^ n - C (u : R)) * (- C ((u⁻¹ : Rˣ) : R)) = (1 : R[X]) := by
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow]
  have hpow : (X : R[X]) ^ (n - 1) * X = X ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hcoeff : C (n : R) * C ((v⁻¹ * u⁻¹ : Rˣ) : R) =
      C ((u⁻¹ : Rˣ) : R) := by
    rw [← map_mul, ← hv, Units.val_mul]
    simp
  calc
    _ = (C (n : R) * C ((v⁻¹ * u⁻¹ : Rˣ) : R)) *
        (X ^ (n - 1) * X) - X ^ n * C ((u⁻¹ : Rˣ) : R) +
        C (u : R) * C ((u⁻¹ : Rˣ) : R) := by ring
    _ = 1 := by
      rw [hcoeff, hpow, mul_comm (C _) (X ^ n), sub_self, zero_add, ← map_mul]
      simp

/-- The explicit standard etale pair for adjoining an n-th root of a unit. -/
def unitRootPair (n : ℕ) (hn : 0 < n) (u v : Rˣ) (hv : (v : R) = (n : R)) :
    StandardEtalePair R where
  f := X ^ n - C (u : R)
  monic_f := monic_X_pow_sub_C _ (Nat.ne_of_gt hn)
  g := 1
  cond := ⟨C ((v⁻¹ * u⁻¹ : Rˣ) : R) * X, - C ((u⁻¹ : Rˣ) : R), 1,
    by simpa using unitRoot_bezout n hn u v hv⟩

/-- Adjoining an n-th root of a unit is etale when n is invertible.
These are exactly the hypotheses used in the characteristic-zero cover. -/
theorem etale_adjoin_unit_root (n : ℕ) (hn : 0 < n) (u : R)
    (hu : IsUnit u) (hnunit : IsUnit (n : R)) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C u)) := by
  obtain ⟨U, rfl⟩ := hu
  obtain ⟨V, hV⟩ := hnunit
  let P := unitRootPair n hn U V hV
  exact Algebra.Etale.of_equiv (standardPairRootEquiv P rfl)

end KummerEtale


/-! Normality of the integral étale coordinate algebras in the Kummer
normalization charts, via smooth base change of integral closure. -/
open scoped TensorProduct
open nonZeroDivisors
namespace EtaleNormal
variable (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra.Etale R S]

lemma base_injective : Function.Injective (algebraMap R S) := by
  have : Module.IsTorsionFree R S := inferInstance
  exact FaithfulSMul.algebraMap_injective R S

abbrev Generic := S ⊗[R] FractionRing R

lemma inverted_le : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
  rintro _ ⟨r, hr, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero
    ((map_ne_zero_iff _ (base_injective R S)).mpr (nonZeroDivisors.ne_zero hr))

instance genericDomain : IsDomain (Generic R S) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _ (inverted_le R S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsDomain S] in
lemma generic_finite : Module.Finite (FractionRing R) (Generic R S) := by
  let e : FractionRing R ⊗[R] S ≃ₐ[FractionRing R] Generic R S :=
    { (Algebra.TensorProduct.comm R (FractionRing R) S).toRingEquiv with
      commutes' := fun _ => rfl }
  have : Algebra.Etale (FractionRing R) (Generic R S) := Algebra.Etale.of_equiv e
  exact Algebra.FormallyUnramified.finite_of_free (FractionRing R) (Generic R S)

lemma generic_isField : IsField (Generic R S) := by
  have := generic_finite R S
  exact isField_of_isIntegral_of_isField' (Field.toIsField (FractionRing R))

/-- The generic algebra is the entire fraction field of the etale domain,
not just a subring of it. -/
lemma generic_fractionRing : IsFractionRing S (Generic R S) := by
  let := (generic_isField R S).toField
  have hi := IsLocalization.injective (Generic R S) (inverted_le R S)
  have : FaithfulSMul S (Generic R S) :=
    (faithfulSMul_iff_algebraMap_injective S (Generic R S)).mpr hi
  apply IsFractionRing.of_field
  intro z
  obtain ⟨⟨x, y⟩, hy⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid S R⁰) z
  refine ⟨x, y, (eq_div_iff ?_).mpr hy⟩
  exact (map_ne_zero_iff _ hi).mpr (nonZeroDivisors.ne_zero (inverted_le R S y.2))

/-- Smooth base change and integral closedness of the base force all
integral elements in the generic fraction algebra to lie in the chart. -/
theorem integrallyClosed [IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  have : IsFractionRing S (Generic R S) := generic_fractionRing R S
  apply (isIntegrallyClosed_iff (Generic R S)).mpr
  intro x hx
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := S) (B := FractionRing R)).surjective ⟨x, hx⟩
  have ht' : (Algebra.TensorProduct.map (AlgHom.id R S)
      (integralClosure R (FractionRing R)).val) t = x := congrArg Subtype.val ht
  rw [← ht']
  clear ht' ht hx x
  induction t using TensorProduct.inductionOn with
  | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, map_add, ha', hb']⟩
  | tmul s y =>
      obtain ⟨r, hr⟩ := (isIntegrallyClosed_iff (FractionRing R)).mp
        ‹IsIntegrallyClosed R› y.2
      refine ⟨s * algebraMap R S r, ?_⟩
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Subalgebra.val_apply, ← hr]
      change (s * algebraMap R S r) ⊗ₜ[R] (1 : FractionRing R) = s ⊗ₜ[R] algebraMap R _ r
      rw [mul_comm s, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one]

end EtaleNormal

namespace KummerEtale
open Polynomial
variable {R : Type*} [CommRing R]

/-- A monic factor of a unit-root equation itself defines an etale algebra.
The Bezout equation is derived, not assumed. -/
theorem etale_monic_factor (n : ℕ) (hn : 0 < n) (u : Rˣ)
    (hnunit : IsUnit (n : R)) (g : R[X]) (hg : g.Monic)
    (hd : g ∣ X ^ n - C (u : R)) : Algebra.Etale R (AdjoinRoot g) := by
  obtain ⟨v, hv⟩ := hnunit
  obtain ⟨q, hq⟩ := hd
  let a : R[X] := C ((v⁻¹ * u⁻¹ : Rˣ) : R) * X
  let b : R[X] := - C ((u⁻¹ : Rˣ) : R)
  have hh : derivative (g * q) * a + g * q * b = 1 := by
    rw [← hq]
    exact unitRoot_bezout n hn u v hv
  let P : StandardEtalePair R :=
    { f := g
      monic_f := hg
      g := 1
      cond := ⟨q * a, derivative q * a + q * b, 1, by
        simp only [pow_one]
        rw [derivative_mul] at hh
        linear_combination hh⟩ }
  exact Algebra.Etale.of_equiv (standardPairRootEquiv P rfl)

variable [IsDomain R] [IsIntegrallyClosed R]
  {L : Type*} [Field L] [Algebra R L] [Module.IsTorsionFree R L]

/-- A chosen root inside a field, rather than the whole potentially
 disconnected root algebra, still provides an etale integral domain cover. -/
theorem etale_adjoin_unit_root_in_field (n : ℕ) (hn : 0 < n) (u : Rˣ)
    (hnunit : IsUnit (n : R)) (x : L) (hx : x ^ n = algebraMap R L (u : R)) :
    Algebra.Etale R (Algebra.adjoin R ({x} : Set L)) := by
  have hz : aeval x (X ^ n - C (u : R)) = 0 := by simp [hx]
  have hi : IsIntegral R x := ⟨X ^ n - C (u : R), monic_X_pow_sub_C _ hn.ne', hz⟩
  have := etale_monic_factor n hn u hnunit (minpoly R x) (minpoly.monic hi)
    (minpoly.isIntegrallyClosed_dvd hi hz)
  exact Algebra.Etale.of_equiv (minpoly.equivAdjoin hi)

end KummerEtale

namespace KummerEtale
universe u
variable (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- A finite free étale domain cover with one prescribed root of a unit. -/
theorem exists_domain_unit_root (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (u : Rˣ) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : Algebra.Etale R S)
      (_ : IsIntegrallyClosed S),
      ∃ c : Sˣ, (c : S) ^ n = algebraMap R S (u : R) := by
  let L := AlgebraicClosure (FractionRing R)
  have : Module.IsTorsionFree R L := by
    apply (Module.isTorsionFree_iff_algebraMap_injective (R := R) (A := L)).mpr
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) L]
    exact (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap R L (u : R)) hn
  let S := Algebra.adjoin R ({x} : Set L)
  have hz : aeval x (X ^ n - C (u : R)) = 0 := by simp [hx]
  have hi : IsIntegral R x := ⟨X ^ n - C (u : R), monic_X_pow_sub_C _ hn.ne', hz⟩
  have : Module.Free R S := Module.Free.of_basis (Algebra.adjoin.powerBasis' hi).basis
  have : Module.Finite R S := Module.Finite.of_basis (Algebra.adjoin.powerBasis' hi).basis
  have : Algebra.Etale R S := etale_adjoin_unit_root_in_field n hn u hnunit x hx
  have : IsIntegrallyClosed S := EtaleNormal.integrallyClosed R S
  let y : S := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  have hy : y ^ n = algebraMap R S (u : R) := Subtype.ext hx
  have hu : IsUnit y := (isUnit_pow_iff hn.ne').mp
    (hy ▸ u.isUnit.map (algebraMap R S))
  refine ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hu.unit, ?_⟩
  simpa using hy

/-- Simultaneously adjoining the five unit factors can be done by a genuine
finite faithfully flat etale integral cover. All roots are actual units. -/
theorem exists_domain_unit_roots (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    {m : ℕ} (u : Fin m → Rˣ) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : Algebra.Etale R S)
      (_ : IsIntegrallyClosed S),
      (Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) ∧
      ∃ c : Fin m → Sˣ, ∀ i, (c i : S) ^ n = algebraMap R S (u i : R) := by
  induction m with
  | zero =>
    refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, ?_, Fin.elim0, fun i => Fin.elim0 i⟩
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  | succ m ih =>
    obtain ⟨S, _, _, _, _, _, _, _, _, c, hc⟩ := ih (fun i => u i.castSucc)
    let w : Sˣ := Units.map (algebraMap R S) (u (Fin.last m))
    obtain ⟨A, _, _, _, _, _, _, _, z, hz⟩ :=
      exists_domain_unit_root S n hn (by simpa using hnunit.map (algebraMap R S)) w
    algebraize [(algebraMap S A).comp (algebraMap R S)]
    have : Module.Finite R A := .trans S A
    have : Module.Free R A := .trans (S := S)
    have : Algebra.Etale R A := .comp R S A
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, PrimeSpectrum.comap_surjective_of_faithfullyFlat,
      Fin.snoc (fun i => Units.map (algebraMap S A) (c i)) z, ?_⟩
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [w, IsScalarTower.algebraMap_apply R S A] using hz
    · simpa [← map_pow, IsScalarTower.algebraMap_apply R S A] using
        congrArg (algebraMap S A) (hc j)

end KummerEtale

namespace KummerEtale
variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  {L : Type*} [Field L] [Algebra R L] [Module.IsTorsionFree R L]

/-- The actual finite subalgebra generated by finitely many unit roots is
finite free and etale. This concerns the fixed roots inside the original
function field, not some unrelated etale cover. -/
theorem finite_unit_roots (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (s : Finset L) (hs : ∀ x ∈ s, ∃ u : Rˣ, x ^ n = algebraMap R L (u : R)) :
    Algebra.Etale R (Algebra.adjoin R (s : Set L)) ∧
    Module.Finite R (Algebra.adjoin R (s : Set L)) ∧
    Module.Free R (Algebra.adjoin R (s : Set L)) ∧
    IsIntegrallyClosed (Algebra.adjoin R (s : Set L)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    let e := (Algebra.botEquivOfInjective
      ((Module.isTorsionFree_iff_algebraMap_injective (R := R) (A := L)).mp inferInstance)).symm.trans
      (Subalgebra.equivOfEq ⊥ (Algebra.adjoin R (↑(∅ : Finset L) : Set L)) (by simp))
    have := Algebra.Etale.of_equiv e
    have := Module.Finite.equiv e.toLinearEquiv
    have := Module.Free.of_equiv e.toLinearEquiv
    have := IsIntegrallyClosed.of_equiv e.toRingEquiv
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  | @insert x s hxs ih =>
    obtain ⟨hE, hF, hFree, hN⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
    let A := Algebra.adjoin R (s : Set L)
    have : Algebra.Etale R A := hE
    have : Module.Finite R A := hF
    have : Module.Free R A := hFree
    have : IsIntegrallyClosed A := hN
    obtain ⟨u, hu⟩ := hs x (Finset.mem_insert_self x s)
    let v : Aˣ := Units.map (algebraMap R A) u
    have hv : x ^ n = algebraMap A L (v : A) := by
      exact hu
    have nh : IsUnit (n : A) := by simpa using hnunit.map (algebraMap R A)
    have : Module.IsTorsionFree A L := by
      exact (Module.isTorsionFree_iff_algebraMap_injective (R := A) (A := L)).mpr
        Subtype.val_injective
    let B := Algebra.adjoin A ({x} : Set L)
    have : Algebra.Etale A B := etale_adjoin_unit_root_in_field n hn v nh x hv
    have hi : IsIntegral A x := ⟨X ^ n - C (v : A),
      monic_X_pow_sub_C _ hn.ne', by simp [hv]⟩
    have : Module.Finite A B := Module.Finite.of_basis (Algebra.adjoin.powerBasis' hi).basis
    have : Module.Free A B := Module.Free.of_basis (Algebra.adjoin.powerBasis' hi).basis
    have : Algebra.Etale R B := .comp R A B
    have : Module.Finite R B := .trans A B
    have : Module.Free R B := .trans (S := A)
    have : IsIntegrallyClosed B := EtaleNormal.integrallyClosed R B
    have hAB : Algebra.adjoin R ((insert x s : Finset L) : Set L) =
        (Algebra.adjoin A ({x} : Set L)).restrictScalars R := by
      rw [Finset.coe_insert, ← Set.singleton_union, Set.union_comm]
      exact Algebra.adjoin_union_eq_adjoin_adjoin R (s : Set L) {x}
    let e : B ≃ₐ[R] Algebra.adjoin R ((insert x s : Finset L) : Set L) :=
      (Subalgebra.equivOfEq _ _ hAB).symm
    have := Algebra.Etale.of_equiv e
    have := Module.Finite.equiv e.toLinearEquiv
    have := Module.Free.of_equiv e.toLinearEquiv
    have := IsIntegrallyClosed.of_equiv e.toRingEquiv
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end KummerEtale

namespace KummerEtale
open nonZeroDivisors
variable {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K] [Algebra R L] [Algebra K L]
  [IsScalarTower R K L]

omit [IsDomain R] in
/-- Generators for the original extension over the fraction field give the
fraction field of their actual integral subalgebra. -/
theorem adjoin_fractionRing (s : Set L) (hs : Algebra.adjoin K s = ⊤) :
    IsFractionRing (Algebra.adjoin R s) L := by
  let B := Algebra.adjoin R s
  let g : FractionRing B →+* L := IsFractionRing.lift (g := B.val.toRingHom)
    (K := FractionRing B) Subtype.val_injective
  have hg (x : B) : g (algebraMap B (FractionRing B) x) = (x : L) :=
    IsFractionRing.lift_algebraMap Subtype.val_injective x
  have hK (x : K) : algebraMap K L x ∈ g.fieldRange := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R x
    rw [map_div₀]
    apply g.fieldRange.div_mem
    · refine ⟨algebraMap B (FractionRing B) (algebraMap R B a), ?_⟩
      rw [hg]
      exact IsScalarTower.algebraMap_apply R K L a
    · refine ⟨algebraMap B (FractionRing B) (algebraMap R B b), ?_⟩
      rw [hg]
      exact IsScalarTower.algebraMap_apply R K L b
  let C : Subalgebra K L := { g.fieldRange.toSubring with algebraMap_mem' := hK }
  have hC : Algebra.adjoin K s ≤ C := by
    refine Algebra.adjoin_le ?_
    intro x hx
    exact ⟨algebraMap B (FractionRing B) ⟨x, Algebra.subset_adjoin hx⟩, hg _⟩
  have hsurj : Function.Surjective g := by
    intro x
    exact hC (by rw [hs]; trivial)
  have : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr
    Subtype.val_injective
  apply IsFractionRing.of_field
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B y
  exact ⟨a, b, by rw [map_div₀, hg, hg]; rfl⟩

variable [IsIntegrallyClosed R] [Module.IsTorsionFree R L]

/-- The whole normalization off the branch divisor is exactly the root
subalgebra and is finite free and etale. All claims concern the SAME field L. -/
theorem normalization_unit_roots (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))
    (s : Finset L) (hs : ∀ x ∈ s, ∃ u : Rˣ, x ^ n = algebraMap R L (u : R))
    (hgen : Algebra.adjoin K (s : Set L) = ⊤) :
    integralClosure R L = Algebra.adjoin R (s : Set L) := by
  obtain ⟨hE, hF, hFree, hN⟩ := finite_unit_roots n hn hnunit s hs
  let B := Algebra.adjoin R (s : Set L)
  have : Module.Finite R B := hF
  have : IsIntegrallyClosed B := hN
  have : IsFractionRing B L := adjoin_fractionRing (K := K) (s : Set L) hgen
  apply le_antisymm
  · intro x hx
    have hx' : IsIntegral B x := ((mem_integralClosure_iff R L).mp hx).tower_top
    obtain ⟨b, hb⟩ := (isIntegrallyClosed_iff L).mp hN hx'
    change (b : L) = x at hb
    exact hb ▸ b.property
  · intro x hx
    exact (mem_integralClosure_iff R L).mpr ((Algebra.IsIntegral.isIntegral (R := R) (⟨x, hx⟩ : B)).map
      B.val)
end KummerEtale

namespace KummerCover
variable {K ι : Type*} [Field K] {p : ℕ} [Fact p.Prime]
noncomputable def chosenRoot (a : K) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) a) (NeZero.pos p)).choose

lemma chosenRoot_pow (a : K) :
    chosenRoot (p := p) a ^ p = algebraMap K (AlgebraicClosure K) a :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) a) (NeZero.pos p)).choose_spec

abbrev rootField (a : ι → K) : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.adjoin K (Set.range fun i => chosenRoot (p := p) (a i))

noncomputable def fieldRoot (a : ι → K) (i : ι) : rootField (p := p) a :=
  ⟨chosenRoot (p := p) (a i), IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩

lemma fieldRoot_pow (a : ι → K) (i : ι) :
    fieldRoot (p := p) a i ^ p = algebraMap K (rootField (p := p) a) (a i) := by
  apply Subtype.ext
  exact chosenRoot_pow (a i)

lemma fieldRoot_generates (a : ι → K) :
    Algebra.adjoin K (Set.range (fieldRoot (p := p) a)) = ⊤ := by
  apply Subalgebra.map_injective (f := (rootField (p := p) a).val)
    (rootField (p := p) a).val.injective
  rw [AlgHom.map_adjoin, ← Set.range_comp, Algebra.map_top, IntermediateField.range_val]
  exact (IntermediateField.adjoin_toSubalgebra _).symm


instance finite_rootField [Finite ι] (a : ι → K) :
    FiniteDimensional K (rootField (p := p) a) := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact Algebra.IsIntegral.isIntegral x
end KummerCover


open scoped BigOperators
namespace KummerLines

abbrev R := MvPolynomial (Fin 2) ℂ
abbrev K := FractionRing R
open MvPolynomial

def lineForm : Fin 5 → R := ![X 0, X 1, X 0 - 1, X 1 - 1, X 0 - X 1]
def point : Fin 5 → (Fin 2 → ℂ) := ![![0, 2], ![2, 0], ![1, 2], ![2, 1], ![2, 2]]
def variableIndex : Fin 5 → Fin 2 := ![0, 1, 0, 1, 0]

lemma coefficient_one (i : Fin 5) :
    (lineForm i).coeff (Finsupp.single (variableIndex i) 1) = 1 := by
  fin_cases i <;> simp [lineForm, variableIndex, MvPolynomial.coeff_X, MvPolynomial.coeff_one, Finsupp.single_left_inj, eq_comm]

lemma degree_le (i : Fin 5) : (lineForm i).totalDegree ≤ 1 := by
  fin_cases i
  · simp [lineForm]
  · simp [lineForm]
  · simpa [lineForm] using totalDegree_sub (X (0 : Fin 2) : R) 1
  · simpa [lineForm] using totalDegree_sub (X (1 : Fin 2) : R) 1
  · simpa [lineForm] using totalDegree_sub (X (0 : Fin 2) : R) (X 1)

lemma degree_eq (i : Fin 5) : (lineForm i).totalDegree = 1 := by
  apply Nat.le_antisymm (degree_le i)
  have hh := le_totalDegree (p := lineForm i)
    (s := Finsupp.single (variableIndex i) 1)
    (by rw [MvPolynomial.mem_support_iff, coefficient_one]; exact one_ne_zero)
  simpa using hh

lemma prime_lineForm (i : Fin 5) : Prime (lineForm i) := by
  apply Irreducible.prime
  apply irreducible_of_totalDegree_eq_one (degree_eq i)
  intro x hx
  exact isUnit_of_dvd_one (by simpa [coefficient_one] using hx (Finsupp.single (variableIndex i) 1))

lemma eval_at_self (i : Fin 5) : eval (point i) (lineForm i) = 0 := by
  fin_cases i <;> norm_num [lineForm, point]

lemma eval_at_other (i j : Fin 5) (h : i ≠ j) : eval (point i) (lineForm j) ≠ 0 := by
  fin_cases i <;> fin_cases j <;> first | exact (h rfl).elim | norm_num [lineForm, point]

lemma pairwise_not_associated : Pairwise fun i j => ¬ Associated (lineForm i) (lineForm j) := by
  intro i j hij ha
  obtain ⟨d, hd⟩ := ha.dvd
  have hh := congrArg (MvPolynomial.eval (point i)) hd
  rw [map_mul, eval_at_self, zero_mul] at hh
  exact eval_at_other i j hij hh

end KummerLines

namespace KummerLines
variable (p : ℕ) [Fact p.Prime]
def radicand (i : Fin 5) : K := algebraMap R K (lineForm i)
abbrev L := KummerCover.rootField (p := p) radicand
instance prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩
end KummerLines


namespace KummerLines
open scoped BigOperators
open nonZeroDivisors

def branchProduct : R := ∏ i : Fin 5, lineForm i
lemma branchProduct_ne_zero : branchProduct ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => (prime_lineForm i).ne_zero)
lemma branchPowers_le : Submonoid.powers branchProduct ≤ R⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n branchProduct_ne_zero)

/-- The literal affine complement of the five branch lines in A². This
subalgebra model keeps the original fraction field C(x,y) definitionally. -/
noncomputable def offBranch : Subalgebra R K :=
  Localization.subalgebra K (Submonoid.powers branchProduct) branchPowers_le
abbrev U := offBranch
instance : IsLocalization.Away branchProduct U :=
  inferInstanceAs (IsLocalization.Away branchProduct
    (Localization.subalgebra K (Submonoid.powers branchProduct) branchPowers_le))
instance : IsFractionRing U K :=
  inferInstanceAs (IsFractionRing
    (Localization.subalgebra K (Submonoid.powers branchProduct) branchPowers_le) K)
instance : IsIntegrallyClosed U :=
  isIntegrallyClosed_of_isLocalization U (Submonoid.powers branchProduct) branchPowers_le

lemma lineForm_unit (i : Fin 5) : IsUnit (algebraMap R U (lineForm i)) :=
  IsLocalization.Away.isUnit_of_dvd (S := U) branchProduct (Finset.dvd_prod_of_mem lineForm (Finset.mem_univ i))

variable (p : ℕ) [Fact p.Prime]
instance : Module.IsTorsionFree U (L p) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  rw [IsScalarTower.algebraMap_eq U K (L p)]
  exact (algebraMap K (L p)).injective.comp Subtype.val_injective

lemma exponent_unit : IsUnit (p : U) := by
  have hC : IsUnit (p : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast (NeZero.ne p))
  have hR : IsUnit (p : R) := by simpa using hC.map (algebraMap ℂ R)
  simpa using hR.map (algebraMap R U)

def rootSet : Finset (L p) := by
  classical
  exact Finset.univ.image (KummerCover.fieldRoot (p := p) radicand)
lemma rootSet_coe : (rootSet p : Set (L p)) = Set.range (KummerCover.fieldRoot (p := p) radicand) := by
  classical
  ext x
  simp [rootSet]

/-- Over the actual open complement of the arrangement, the normalization
is generated as a finite algebra by the original five roots. -/
theorem offBranch_normalization :
    integralClosure U (L p) = Algebra.adjoin U
      (Set.range (KummerCover.fieldRoot (p := p) radicand)) := by
  rw [← rootSet_coe]
  apply KummerEtale.normalization_unit_roots (K := K) p (NeZero.pos p) (exponent_unit p)
  · intro x hx
    classical
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    refine ⟨(lineForm_unit i).unit, ?_⟩
    rw [IsUnit.unit_spec]
    exact KummerCover.fieldRoot_pow radicand i
  · rw [rootSet_coe]
    exact KummerCover.fieldRoot_generates radicand
abbrev offBranchCover := integralClosure U (L p)

/-- The actual unramified part of the source cover is finite free etale,
not just normal or a finite extension generically. -/
theorem offBranchCover_finiteFreeEtale :
    Module.Finite U (offBranchCover p) ∧ Module.Free U (offBranchCover p) ∧
      Algebra.Etale U (offBranchCover p) := by
  have hs : ∀ x ∈ rootSet p, ∃ u : Uˣ, x ^ p = algebraMap U (L p) (u : U) := by
    intro x hx
    classical
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (show x ∈ Finset.univ.image _ from hx)
    refine ⟨(lineForm_unit i).unit, ?_⟩
    rw [IsUnit.unit_spec]
    exact KummerCover.fieldRoot_pow radicand i
  obtain ⟨hE, hF, hFree, -⟩ := KummerEtale.finite_unit_roots
    p (NeZero.pos p) (exponent_unit p) (rootSet p) hs
  rw [rootSet_coe] at hE hF hFree
  unfold offBranchCover
  rw [offBranch_normalization]
  exact ⟨hF, hFree, hE⟩

/-- The normalized cover over the complement of the branch lines is smooth
over the complex numbers. -/
theorem offBranchCover_smooth : Algebra.Smooth ℂ (offBranchCover p) := by
  have : Algebra.Etale R U := Algebra.Etale.of_isLocalizationAway branchProduct
  have : Algebra.Smooth ℂ R := ⟨inferInstance, inferInstance⟩
  have : Algebra.Smooth ℂ U := Algebra.Smooth.comp ℂ R U
  have : Algebra.Etale U (offBranchCover p) := (offBranchCover_finiteFreeEtale p).2.2
  exact Algebra.Smooth.comp ℂ U (offBranchCover p)

/-- The finite etale cover is surjective on the actual branch-complement
spectrum; no point has been removed from this locus upstairs. -/
theorem offBranchCover_surjective :
    Function.Surjective (PrimeSpectrum.comap (algebraMap U (offBranchCover p))) := by
  have : Nontrivial (offBranchCover p) :=
    ⟨⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩⟩
  have : Module.Free U (offBranchCover p) := (offBranchCover_finiteFreeEtale p).2.1
  have : Module.FaithfullyFlat U (offBranchCover p) :=
    Module.FaithfullyFlat.instOfNontrivialOfFree U (offBranchCover p)
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := U) (B := offBranchCover p)
end KummerLines

open IsLocalRing
namespace EtaleRegular

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]

lemma dim_le_of_flat_local [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [Module.Flat R S] : ringKrullDim R ≤ ringKrullDim S := by
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := by
    constructor
    exact (IsLocalRing.maximalIdeal_comap (algebraMap R S)).symm
  rw [← maximalIdeal_height_eq_ringKrullDim (R := R),
    ← maximalIdeal_height_eq_ringKrullDim (R := S)]
  exact WithBot.coe_le_coe.mpr (by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R)
      (maximalIdeal S)]
    exact le_self_add)

theorem regular_local [IsRegularLocalRing R] [IsNoetherianRing S]
    [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Algebra.EssFiniteType R S]
    [Module.Flat R S] [Algebra.FormallyUnramified R S] : IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc
    ((maximalIdeal S).spanFinrank : WithBot ℕ∞) =
        ((maximalIdeal R).map (algebraMap R S)).spanFinrank := by
      rw [Algebra.FormallyUnramified.map_maximalIdeal]
    _ ≤ (maximalIdeal R).spanFinrank := by
      exact_mod_cast Ideal.spanFinrank_map_le_of_fg (algebraMap R S)
        (IsNoetherian.noetherian _)
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ ≤ ringKrullDim S := dim_le_of_flat_local R S

/-- Etale coordinate algebras preserve regularity at every prime. -/
theorem regular [IsRegularRing R] [Algebra.Etale R S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  apply isRegularRing_iff.mpr
  intro q hq
  let p := q.under R
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p q (algebraMap R S) Ideal.LiesOver.over
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.comp R S _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    Algebra.EssFiniteType.of_comp R _ _
  exact regular_local (Localization.AtPrime p) (Localization.AtPrime q)

end EtaleRegular
namespace KummerLines
variable (p : ℕ) [Fact p.Prime]
theorem offBranchCover_regular : IsRegularRing (offBranchCover p) := by
  have : Algebra.Etale R U := Algebra.Etale.of_isLocalizationAway branchProduct
  have : IsRegularRing U := EtaleRegular.regular R U
  have : Algebra.Etale U (offBranchCover p) := (offBranchCover_finiteFreeEtale p).2.2
  exact EtaleRegular.regular U (offBranchCover p)
end KummerLines

namespace KummerLines
open scoped TensorProduct
variable (p : ℕ) [Fact p.Prime]
/-- Restricting the normalization of the actual original affine plane to
its branch complement gives the same literal finite etale cover. This is
an isomorphism of algebras, not only a generic-field identification. -/
def offBranchRestrictionEquiv :
    U ⊗[R] integralClosure R (L p) ≃ₐ[U] offBranchCover p := by
  have : Algebra.Etale R U := Algebra.Etale.of_isLocalizationAway branchProduct
  exact (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R U (L p))
      TensorProduct.toIntegralClosure_bijective_of_smooth).trans
    (IsLocalization.algebraLid (Submonoid.powers branchProduct) U (L p)).mapIntegralClosure

/-- All points of the original normalized cover away from the branch
locus are regular. No replacement of the original five-root field or
hypothesis of normality/regularity of its normalization occurs. -/
theorem normalization_offBranch_regular :
    IsRegularRing (U ⊗[R] integralClosure R (L p)) := by
  have : IsRegularRing (offBranchCover p) := offBranchCover_regular p
  exact IsRegularRing.of_ringEquiv (R := offBranchCover p)
    (offBranchRestrictionEquiv p).symm.toRingEquiv
end KummerLines


end


noncomputable section
open Algebra Set Cardinal MvPolynomial
namespace AlgebraicIndependent
open scoped _root_.AlgebraicIndependent
/-- For a finite family, independence of polynomial expressions in its
members forces independence of the original generators. This is the
finite transcendence-degree converse needed for the actual ramified
Kummer coordinate charts. -/
lemma of_polynomial_expressions {k A ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Finite ι] {x y : ι → A}
    (hy : AlgebraicIndependent k y)
    (hmem : ∀ i, y i ∈ Algebra.adjoin k (Set.range x)) :
    AlgebraicIndependent k x := by
  let B := Algebra.adjoin k (Set.range x)
  let xB : ι → B := fun i => ⟨x i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  let yB : ι → B := fun i => ⟨y i, hmem i⟩
  have hyB : AlgebraicIndependent k yB := hy.of_comp B.val
  have hgen : Algebra.adjoin k (Set.range xB) = ⊤ := by
    apply Subalgebra.map_injective (f := B.val) Subtype.val_injective
    rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val]
    rw [← Set.range_comp]
    rfl
  let : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range xB)) B := by
    constructor
    intro z
    have hz : z ∈ Algebra.adjoin k (Set.range xB) := by rw [hgen]; trivial
    exact isAlgebraic_algebraMap (⟨z, hz⟩ : Algebra.adjoin k (Set.range xB))
  have hxB : AlgebraicIndependent k xB :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k xB
      hyB.cardinalMk_le_trdeg).1
  exact hxB.map (f := B.val) Subtype.val_injective.injOn

/-- Independent powers of finitely many elements give independent roots. -/
lemma of_powers {k A ι : Type} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Finite ι] {x : ι → A} (n : ι → ℕ)
    (h : AlgebraicIndependent k (fun i => x i ^ n i)) :
    AlgebraicIndependent k x :=
  _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h (fun i =>
    Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _)
end AlgebraicIndependent

end


noncomputable section
open Algebra MvPolynomial
namespace KummerTriple
open KummerLines
variable (p : ℕ) [Fact p.Prime]
local instance : IsScalarTower ℂ R (L p) := IsScalarTower.of_algebraMap_eq' rfl

abbrev root (i : Fin 5) : L p := KummerCover.fieldRoot (p := p) radicand i
lemma root_pow (i : Fin 5) : root p i ^ p = algebraMap R (L p) (lineForm i) :=
  KummerCover.fieldRoot_pow radicand i
lemma root_ne_zero (i : Fin 5) : root p i ≠ 0 := by
  intro h
  have hz := root_pow p i
  rw [h, zero_pow (NeZero.ne p)] at hz
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  exact (prime_lineForm i).ne_zero (hi (hz.symm.trans (map_zero (algebraMap R (L p))).symm))

/-- Coordinates at the exceptional divisor over the actual triple point
(0,0): u is the original root of x, v is root(y)/root(x). -/
def coordinateRoot : Fin 2 → L p := ![root p 0, root p 1 / root p 0]
lemma coordinateRoot_zero_pow : coordinateRoot p 0 ^ p = algebraMap R (L p) (X 0) :=
  root_pow p 0
lemma coordinateRoot_one_pow : coordinateRoot p 1 ^ p =
    algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0) := by
  change (root p 1 / root p 0) ^ p = _
  rw [div_pow, root_pow, root_pow]
  rfl
lemma original_root_one : root p 1 = coordinateRoot p 0 * coordinateRoot p 1 := by
  change root p 1 = root p 0 * (root p 1 / root p 0)
  field_simp [root_ne_zero p 0]

lemma coordinateRoot_independent : AlgebraicIndependent ℂ (coordinateRoot p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
  intro i
  have hu : coordinateRoot p 0 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 0)
  have hv : coordinateRoot p 1 ∈ Algebra.adjoin ℂ (Set.range (coordinateRoot p)) :=
    Algebra.subset_adjoin (Set.mem_range_self 1)
  fin_cases i
  · change algebraMap R (L p) (X 0) ∈ _
    rw [← coordinateRoot_zero_pow p]
    exact Subalgebra.pow_mem _ hu _
  · change algebraMap R (L p) (X 1) ∈ _
    change algebraMap R (L p) (lineForm 1) ∈ _
    rw [← root_pow p 1, original_root_one p]
    exact Subalgebra.pow_mem _ (Subalgebra.mul_mem _ hu hv) _

/-- The x-chart of the blowup of the original plane at (0,0).
Its coordinates s,t map to x,y/x, and the blowdown is x=s,y=st. -/
def C := MvPolynomial (Fin 2) ℂ
instance : CommRing C := inferInstanceAs (CommRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra ℂ C := inferInstanceAs (Algebra ℂ (MvPolynomial (Fin 2) ℂ))
instance : IsRegularRing C := inferInstanceAs (IsRegularRing (MvPolynomial (Fin 2) ℂ))
instance : Algebra.FiniteType ℂ C := inferInstanceAs (Algebra.FiniteType ℂ (MvPolynomial (Fin 2) ℂ))
def blowdown : R →ₐ[ℂ] C := MvPolynomial.aeval ![X 0, X 0 * X 1]
instance : Algebra R C := blowdown.toRingHom.toAlgebra
instance : IsScalarTower ℂ R C :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap blowdown).symm

def chartMap : C →ₐ[ℂ] L p := MvPolynomial.aeval ![
  algebraMap R (L p) (X 0), algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)]
instance : Algebra C (L p) := (chartMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (L p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (chartMap p)).symm
lemma chartMap_blowdown : (chartMap p).comp blowdown = IsScalarTower.toAlgHom ℂ R (L p) := by
  apply MvPolynomial.algHom_ext
  intro i
  have hb : blowdown (X i) = ![(X 0 : C), X 0 * X 1] i := by
    simp only [blowdown]
    exact MvPolynomial.aeval_X (R := ℂ) (S₁ := C) _ i
  have hc (j : Fin 2) : (chartMap p) (X j) =
      ![algebraMap R (L p) (X 0),
        algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)] j :=
    MvPolynomial.aeval_X (R := ℂ) (S₁ := L p) _ j
  refine (congrArg (chartMap p) hb).trans ?_
  fin_cases i
  · exact hc 0
  · refine (map_mul (chartMap p) (X 0 : C) (X 1 : C)).trans ?_
    refine (congrArg₂ (fun x y : L p => x * y) (hc 0) (hc 1)).trans ?_
    have hx : algebraMap R (L p) (X 0) ≠ 0 := by
      change algebraMap R (L p) (lineForm 0) ≠ 0
      rw [← root_pow p 0]
      exact pow_ne_zero _ (root_ne_zero p 0)
    exact mul_div_cancel₀ _ hx

instance : IsScalarTower R C (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (chartMap_blowdown p).symm)

lemma chartMap_injective : Function.Injective (chartMap p) := by
  have hi : Function.Injective (algebraMap R (L p)) := by
    rw [IsScalarTower.algebraMap_eq R K (L p)]
    exact (algebraMap K (L p)).injective.comp (IsFractionRing.injective R K)
  have h := (algebraicIndependent_X (Fin 2) ℂ).map
    (f := IsScalarTower.toAlgHom ℂ R (L p)) hi.injOn
  have hc : AlgebraicIndependent ℂ ![algebraMap R (L p) (X 0),
      algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)] := by
    apply _root_.OAI.AlgebraicIndependent.of_polynomial_expressions h
    intro i
    have hs : algebraMap R (L p) (X 0) ∈ Algebra.adjoin ℂ
        (Set.range ![algebraMap R (L p) (X 0),
          algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)]) :=
      Algebra.subset_adjoin ⟨0, rfl⟩
    have ht : algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0) ∈
        Algebra.adjoin ℂ (Set.range ![algebraMap R (L p) (X 0),
          algebraMap R (L p) (X 1) / algebraMap R (L p) (X 0)]) :=
      Algebra.subset_adjoin ⟨1, rfl⟩
    fin_cases i
    · exact hs
    · have hx : algebraMap R (L p) (X 0) ≠ 0 := by
        change algebraMap R (L p) (lineForm 0) ≠ 0
        rw [← root_pow p 0]
        exact pow_ne_zero _ (root_ne_zero p 0)
      change algebraMap R (L p) (X 1) ∈ _
      simpa only [mul_div_cancel₀ _ hx] using Subalgebra.mul_mem _ hs ht
  exact hc

/-- The two ramified coordinates form an actual polynomial plane in the
original field. No independent auxiliary Kummer field is substituted. -/
def coordinateAlgebra : Subalgebra ℂ (L p) :=
  Algebra.adjoin ℂ (Set.range (coordinateRoot p))
abbrev B := coordinateAlgebra p
def planeEquiv : C ≃ₐ[ℂ] B p := (coordinateRoot_independent p).aevalEquiv
instance : IsRegularRing (B p) :=
  IsRegularRing.of_ringEquiv (planeEquiv p).toRingEquiv
instance : IsIntegrallyClosed (B p) := by
  have hC : IsIntegrallyClosed C :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed (A := MvPolynomial (Fin 2) ℂ)
  exact IsIntegrallyClosed.of_equiv (R := C) (S := B p) (planeEquiv p).toRingEquiv

def bRoot (i : Fin 2) : B p :=
  ⟨coordinateRoot p i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
def planeMap : C →ₐ[ℂ] B p := MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p]
lemma planeMap_comp : (coordinateAlgebra p).val.comp (planeMap p) = chartMap p := by
  apply MvPolynomial.algHom_ext
  intro i
  change (coordinateAlgebra p).val (MvPolynomial.aeval ![bRoot p 0 ^ p, bRoot p 1 ^ p] (X i)) = _
  simp only [chartMap, MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
instance : Algebra C (B p) := (planeMap p).toRingHom.toAlgebra
instance : IsScalarTower ℂ C (B p) :=
  IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap (planeMap p)).symm
instance : IsScalarTower C (B p) (L p) :=
  IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (planeMap_comp p).symm)

lemma coordinateRoot_pow (i : Fin 2) :
    coordinateRoot p i ^ p = algebraMap C (L p) (X i) := by
  change coordinateRoot p i ^ p = MvPolynomial.aeval _ (X i)
  rw [MvPolynomial.aeval_X]
  fin_cases i
  · exact coordinateRoot_zero_pow p
  · exact coordinateRoot_one_pow p
lemma coordinateRoot_integral (i : Fin 2) : IsIntegral C (coordinateRoot p i) := by
  refine ⟨(Polynomial.X : Polynomial C) ^ p - Polynomial.C (R := C) (X i),
    Polynomial.monic_X_pow_sub_C _ (NeZero.ne p), ?_⟩
  change Polynomial.aeval (coordinateRoot p i) _ = 0
  erw [map_sub, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C (R := C) (A := L p)]
  exact sub_eq_zero.mpr (coordinateRoot_pow p i)
instance : Algebra.IsIntegral C (B p) := by
  have hB : coordinateAlgebra p ≤ (integralClosure C (L p)).restrictScalars ℂ := by
    apply Algebra.adjoin_le
    rintro z ⟨i, rfl⟩
    exact coordinateRoot_integral p i
  constructor
  intro b
  have hi : IsIntegral C (b : L p) := hB b.property
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom C (B p) (L p))
    Subtype.val_injective).mp hi
instance : Algebra.FiniteType ℂ (B p) :=
  Algebra.FiniteType.of_surjective (planeEquiv p).toAlgHom (planeEquiv p).surjective
instance : Algebra.FiniteType C (B p) := Algebra.FiniteType.of_restrictScalars_finiteType ℂ C (B p)
instance : Module.Finite C (B p) := Algebra.IsIntegral.finite
end KummerTriple

end

end OAI
