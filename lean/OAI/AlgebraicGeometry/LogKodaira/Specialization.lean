import Mathlib
import OAI.AlgebraicGeometry.LogKodaira.RelativeCanonical

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

def specializeCanonical
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Canonical R B (n + r) →ₗ[B] Canonical S C r :=
  (exteriorDifferentialMap A S B C r).comp
    (basedRelativeCanonicalEquiv R A B n r b c).toLinearMap

 
def specializePluricanonical
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Pluricanonical R B (n + r) m →ₗ[B] Pluricanonical S C r m :=
  tensorScalarMap B C _ _ (specializeCanonical R A B S C n r b c) m

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange BasedRelativeCanonical

lemma differential_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (x : KaehlerDifferential A B) :
    KaehlerDifferential.map A S B' C (KaehlerDifferential.map A A B B' x) =
      KaehlerDifferential.map A S B C x := by
  have h : ((KaehlerDifferential.map A S B' C).restrictScalars B).comp
      (KaehlerDifferential.map A A B B') = KaehlerDifferential.map A S B C := by
    apply LinearMap.ext_on (KaehlerDifferential.span_range_derivation A B)
    rintro _ ⟨b, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    rw [IsScalarTower.algebraMap_apply B B' C]
  exact LinearMap.congr_fun h x

lemma exterior_map_fiber_tower
    (A B B' S C : Type*) [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra A B] [Algebra A B'] [Algebra B B'] [IsScalarTower A B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] (r : ℕ) :
    ((exteriorDifferentialMap A S B' C r).restrictScalars B).comp
      (exteriorDifferentialMap A A B B' r) = exteriorDifferentialMap A S B C r := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span B r (KaehlerDifferential A B))
  rintro _ ⟨v, rfl⟩
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    exteriorDifferentialMap, exteriorScalarMap_wedge]
  congr 1
  funext i
  exact differential_map_fiber_tower A B B' S C (v i)

lemma canonical_specialization_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B')) :
    ((specializeCanonical R A B' S C n r b c').restrictScalars B).comp
        (exteriorDifferentialMap R R B B' (n + r)) =
      specializeCanonical R A B S C n r b c := by
  apply LinearMap.ext
  intro x
  have hnat := LinearMap.congr_fun
    (based_relative_canonical_naturality R A B B' n r b c c') x
  have hcomp := LinearMap.congr_fun (exterior_map_fiber_tower A B B' S C r)
    (basedRelativeCanonicalEquiv R A B n r b c x)
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    LinearEquiv.coe_coe] at hnat hcomp
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    specializeCanonical, LinearEquiv.coe_coe]
  rw [hnat, hcomp]

 

theorem pluricanonical_specialization_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [CommRing C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B')) :
    ((specializePluricanonical R A B' S C n r m b c').restrictScalars B).comp
        (pluricanonicalMap R R B B' (n + r) m) =
      specializePluricanonical R A B S C n r m b c := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change specializePluricanonical R A B' S C n r m b c'
      (pluricanonicalMap R R B B' (n + r) m (PiTensorProduct.tprod B v)) =
    specializePluricanonical R A B S C n r m b c (PiTensorProduct.tprod B v)
  simp only [specializePluricanonical, pluricanonicalMap,
    tensorScalarMap, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.coe_restrictScalars]
  change PiTensorProduct.tprod C (fun i => specializeCanonical R A B' S C n r b c'
      (exteriorDifferentialMap R R B B' (n + r) (v i))) =
    PiTensorProduct.tprod C (fun i => specializeCanonical R A B S C n r b c (v i))
  congr 1
  funext i
  exact LinearMap.congr_fun
    (canonical_specialization_naturality R A B B' S C n r b c c') (v i)

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FractionalCanonical
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

lemma exists_absolute_basis
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Nonempty (Module.Basis (Fin (n + r)) B (KaehlerDifferential R B)) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (KaehlerDifferential.map R A B B) LinearMap.id (KaehlerDifferential.map_surjective R A B)
  exact ⟨(adaptedBasis (KaehlerDifferential.mapBaseChange R A B)
    (KaehlerDifferential.map R A B B) s (formallySmooth_mapBaseChange_injective R A B)
    (KaehlerDifferential.exact_mapBaseChange_map R A B) hs (b.baseChange B) c).reindex
      finSumFinEquiv⟩

lemma free_pluricanonical_injective
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsDomain B] [IsFractionRing B K] [Module.Free B (KaehlerDifferential R B)]
    (n m : ℕ) : Function.Injective (pluricanonicalMap R R B K n m) := by
  classical
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := K) (nonZeroDivisors B)
  let b := Module.Free.chooseBasis B (KaehlerDifferential R B)
  let : LinearOrder (Module.Free.ChooseBasisIndex B (KaehlerDifferential R B)) :=
    linearOrderOfSTO WellOrderingRel
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R B K
  let c := (b.baseChange K).map e
  have hc (i) : c i = KaehlerDifferential.map R R B K (b i) := by
    simp [c, e, Module.Basis.baseChange_apply,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
  have hw (s) : exteriorDifferentialMap R R B K n (b.exteriorPower n s) =
      c.exteriorPower n s := by
    simp only [exteriorPower.coe_basis, exteriorPower.ιMulti_family,
      exteriorDifferentialMap, exteriorScalarMap_wedge]
    congr 1
    funext i
    exact (hc _).symm
  let bb := Basis.piTensorProduct (fun _ : Fin m => b.exteriorPower n)
  let cc := Basis.piTensorProduct (fun _ : Fin m => c.exteriorPower n)
  have hh : (pluricanonicalMap R R B K n m) ∘ bb = cc := by
    funext s
    simp only [Function.comp_apply, bb, cc, Basis.piTensorProduct_apply,
      pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
      MultilinearMap.compLinearMap_apply, hw]
    rfl
  have hli : LinearIndependent B ((pluricanonicalMap R R B K n m) ∘ bb) := by
    rw [hh]
    exact cc.linearIndependent.restrict_scalars' B
  have heq : bb.constr B ((pluricanonicalMap R R B K n m) ∘ bb) =
      pluricanonicalMap R R B K n m := by
    apply bb.ext
    intro i
    simp
  rw [← heq]
  exact bb.injective_constr_of_linearIndependent hli

 

theorem based_pluricanonical_injective
    (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) :
    Function.Injective (pluricanonicalMap R R B K (n + r) m) := by
  obtain ⟨d⟩ := exists_absolute_basis R A B n r b c
  let : Module.Free B (KaehlerDifferential R B) := Module.Free.of_basis d
  exact free_pluricanonical_injective R B K (n + r) m

end ReverseLogKodaira.FractionalCanonical

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

 

def logarithmicPullback
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    (n m : ℕ) (t : B) : Pluricanonical R B n m →ₗ[B] Pluricanonical R K n m :=
  ((algebraMap B K t)^m)⁻¹ • pluricanonicalMap R R B K n m

 

def logarithmicSpecialize
    (R A B S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [Algebra.FormallySmooth A B] (n r m : ℕ)
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t : B) :
    Pluricanonical R B (n + r) m →ₗ[B] Pluricanonical S C r m :=
  ((algebraMap B C t)^m)⁻¹ • specializePluricanonical R A B S C n r m b c

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

lemma pluricanonical_map_tower
    (R B B' K : Type*) [CommRing R] [CommRing B] [CommRing B'] [CommRing K]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    (n m : ℕ) :
    ((pluricanonicalMap R R B' K n m).restrictScalars B).comp
      (pluricanonicalMap R R B B' n m) = pluricanonicalMap R R B K n m := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change pluricanonicalMap R R B' K n m
      (pluricanonicalMap R R B B' n m (PiTensorProduct.tprod B v)) =
    pluricanonicalMap R R B K n m (PiTensorProduct.tprod B v)
  simp only [pluricanonicalMap, tensorScalarMap, PiTensorProduct.lift.tprod,
    MultilinearMap.compLinearMap_apply, MultilinearMap.coe_restrictScalars]
  congr 1
  funext i
  exact LinearMap.congr_fun (exterior_map_fiber_tower R B B' R K n) (v i)

lemma logarithmicPullback_naturality
    (R B B' K : Type*) [CommRing R] [CommRing B] [CommRing B'] [Field K]
    [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    (n m : ℕ) (t : B) (u : Pluricanonical R B n m) :
    logarithmicPullback R B' K n m (algebraMap B B' t)
      (pluricanonicalMap R R B B' n m u) = logarithmicPullback R B K n m t u := by
  have h := LinearMap.congr_fun (pluricanonical_map_tower R B B' K n m) u
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  simp only [logarithmicPullback, LinearMap.smul_apply,
    ← IsScalarTower.algebraMap_apply B B' K, h]

lemma logarithmicSpecialize_naturality
    (R A B B' S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B'))
    (t : B) (u : Pluricanonical R B (n + r) m) :
    logarithmicSpecialize R A B' S C n r m b c' (algebraMap B B' t)
      (pluricanonicalMap R R B B' (n + r) m u) =
    logarithmicSpecialize R A B S C n r m b c t u := by
  have h := LinearMap.congr_fun
    (pluricanonical_specialization_naturality R A B B' S C n r m b c c') u
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at h
  simp only [logarithmicSpecialize, LinearMap.smul_apply,
    ← IsScalarTower.algebraMap_apply B B' C, h]

lemma logarithmicPullback_injective
    (R A B K : Type*) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t : B) (ht : t ≠ 0) :
    Function.Injective (logarithmicPullback R B K (n + r) m t) := by
  intro u v huv
  apply based_pluricanonical_injective R A B K n r m b c
  have htK : algebraMap B K t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne ht
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero m htK))) huv

 

theorem logarithmic_specialization_chart_independent
    (R A B B' K S C : Type*) [CommRing R] [CommRing A] [CommRing B] [CommRing B']
    [Field K] [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra A B'] [Algebra R B'] [IsScalarTower R A B']
    [Algebra B B'] [IsScalarTower A B B'] [IsScalarTower R B B']
    [Algebra R K] [Algebra B K] [Algebra B' K]
    [IsScalarTower R B K] [IsScalarTower R B' K] [IsScalarTower B B' K]
    [IsDomain B'] [IsFractionRing B' K]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra B' C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A B' C] [IsScalarTower B B' C]
    [IsScalarTower A S C] [Algebra.FormallySmooth A B] [Algebra.FormallySmooth A B']
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (c' : Module.Basis (Fin r) B' (KaehlerDifferential A B'))
    (t : B) (ht : algebraMap B B' t ≠ 0)
    (u : Pluricanonical R B (n + r) m) (v : Pluricanonical R B' (n + r) m)
    (h : logarithmicPullback R B K (n + r) m t u =
      logarithmicPullback R B' K (n + r) m (algebraMap B B' t) v) :
    logarithmicSpecialize R A B S C n r m b c t u =
      logarithmicSpecialize R A B' S C n r m b c' (algebraMap B B' t) v := by
  have hv : pluricanonicalMap R R B B' (n + r) m u = v := by
    apply logarithmicPullback_injective R A B' K n r m b c' _ ht
    rw [logarithmicPullback_naturality]
    exact h
  rw [← hv, logarithmicSpecialize_naturality]

end ReverseLogKodaira.LogarithmicSpecialization

namespace ReverseLogKodaira.LogarithmicSpecialization
open DifferentialBaseChange BasedRelativeCanonical CanonicalSpecialization FractionalCanonical

 

theorem logarithmic_specialization_equation_independent
    (R A B K S C : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Field K] [CommRing S] [Field C]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    [Algebra A S] [Algebra A C] [Algebra B C] [Algebra S C]
    [IsScalarTower A B C] [IsScalarTower A S C]
    [IsDomain B] [IsFractionRing B K] [Algebra.FormallySmooth A B]
    (n r m : ℕ) (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B)) (t v : B)
    (ht : algebraMap B C t ≠ 0) (hv : algebraMap B C v ≠ 0)
    (u w : Pluricanonical R B (n + r) m)
    (heq : logarithmicPullback R B K (n + r) m t u =
      logarithmicPullback R B K (n + r) m v w) :
    logarithmicSpecialize R A B S C n r m b c t u =
      logarithmicSpecialize R A B S C n r m b c v w := by
  have htB : t ≠ 0 := by intro h; apply ht; simp [h]
  have hvB : v ≠ 0 := by intro h; apply hv; simp [h]
  have htK : algebraMap B K t ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne htB
  have hvK : algebraMap B K v ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne hvB
  have h1 : pluricanonicalMap R R B K (n + r) m u =
      (algebraMap B K t)^m •
        ((algebraMap B K v)^m)⁻¹ • pluricanonicalMap R R B K (n + r) m w :=
    (inv_smul_eq_iff₀ (pow_ne_zero m htK)).mp heq
  have hcross : v^m • u = t^m • w := by
    apply based_pluricanonical_injective R A B K n r m b c
    simp only [map_smul]
    rw [← IsScalarTower.algebraMap_smul K (v^m),
      ← IsScalarTower.algebraMap_smul K (t^m), map_pow, map_pow]
    calc
      (algebraMap B K v)^m • pluricanonicalMap R R B K (n + r) m u =
          (algebraMap B K v)^m • ((algebraMap B K t)^m •
            ((algebraMap B K v)^m)⁻¹ • pluricanonicalMap R R B K (n + r) m w) :=
        congrArg ((algebraMap B K v)^m • ·) h1
      _ = (algebraMap B K t)^m •
          ((algebraMap B K v)^m • ((algebraMap B K v)^m)⁻¹ •
            pluricanonicalMap R R B K (n + r) m w) := smul_comm _ _ _
      _ = (algebraMap B K t)^m • pluricanonicalMap R R B K (n + r) m w := by
        rw [smul_inv_smul₀ (pow_ne_zero m hvK)]
  have hc := congrArg (specializePluricanonical R A B S C n r m b c) hcross
  simp only [map_smul] at hc
  rw [← IsScalarTower.algebraMap_smul C (v^m),
    ← IsScalarTower.algebraMap_smul C (t^m), map_pow, map_pow] at hc
  apply smul_right_injective _ (mul_ne_zero (pow_ne_zero m ht) (pow_ne_zero m hv))
  simp only [logarithmicSpecialize, LinearMap.smul_apply, smul_smul]
  have htc : ((algebraMap B C t)^m * (algebraMap B C v)^m) *
      ((algebraMap B C t)^m)⁻¹ = (algebraMap B C v)^m := by
    field_simp
  have hvc : ((algebraMap B C t)^m * (algebraMap B C v)^m) *
      ((algebraMap B C v)^m)⁻¹ = (algebraMap B C t)^m := by
    field_simp
  rw [htc, hvc]
  exact hc

end ReverseLogKodaira.LogarithmicSpecialization

end

end OAI
