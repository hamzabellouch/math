import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.ActionDenominators

namespace OAI

/-! Plane-origin coordinate rings, stalk lattices and overlap evaluation. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section

variable (k : Type*) [Field k]

abbrev planeCoordinateRing := MvPolynomial (Fin 2) k

def planeOriginIdeal : Ideal (planeCoordinateRing k) :=
  RingHom.ker MvPolynomial.constantCoeff

instance planeOriginIdeal_isMaximal : (planeOriginIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun a => ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C (Fin 2) a⟩)

lemma planeOriginIdeal_eq_span : planeOriginIdeal k =
    Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)} := by
  have hvars : planeOriginIdeal k = MvPolynomial.idealOfVars (Fin 2) k := by
    ext f
    change f.coeff 0 = 0 ↔ f ∈ MvPolynomial.idealOfVars (Fin 2) k
    have he := MvPolynomial.mem_pow_idealOfVars_iff' (R := k) (σ := Fin 2) 1 f
    simpa only [pow_one, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff,
      forall_eq] using he.symm
  rw [hvars, MvPolynomial.idealOfVars]
  congr 1
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩

abbrev planeOriginRing := Localization.AtPrime (planeOriginIdeal k)

abbrev planeOriginCoordinate (i : Fin 2) : planeOriginRing k :=
  algebraMap (planeCoordinateRing k) (planeOriginRing k) (MvPolynomial.X i)

lemma planeOriginCoordinate_ne_zero (i : Fin 2) : planeOriginCoordinate k i ≠ 0 := by
  exact fun h => MvPolynomial.X_ne_zero i
    ((IsLocalization.injective (planeOriginRing k)
      (planeOriginIdeal k).primeCompl_le_nonZeroDivisors) (h.trans (map_zero _).symm))

lemma planeOrigin_maximalIdeal : IsLocalRing.maximalIdeal (planeOriginRing k) =
    Ideal.span {planeOriginCoordinate k 0, planeOriginCoordinate k 1} := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (planeOriginIdeal k) (planeOriginRing k)]
  calc
    _ = Ideal.map (algebraMap (planeCoordinateRing k) (planeOriginRing k))
        (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X (1 : Fin 2)}) :=
      congrArg (Ideal.map (algebraMap (planeCoordinateRing k) (planeOriginRing k)))
        (planeOriginIdeal_eq_span k)
    _ = _ := by
      rw [Ideal.map_span]
      simp only [Set.image_insert_eq, Set.image_singleton, planeOriginCoordinate]

lemma planeOriginCoordinate_prime (i : Fin 2) : Prime (planeOriginCoordinate k i) := by
  apply (IsLocalization.toLocalizationMap (planeOriginIdeal k).primeCompl
    (planeOriginRing k)).map_prime (MvPolynomial.X_prime (i := i)) (planeOriginCoordinate_ne_zero k i)
  change ¬ IsUnit (planeOriginCoordinate k i)
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (planeOriginRing k) (planeOriginIdeal k)]
  change ¬ (MvPolynomial.X i : planeCoordinateRing k) ∉ planeOriginIdeal k
  simp [planeOriginIdeal, RingHom.mem_ker]

lemma planeOriginCoordinates_relPrime :
    IsRelPrime (planeOriginCoordinate k 0) (planeOriginCoordinate k 1) := by
  apply (planeOriginCoordinate_prime k 0).irreducible.isRelPrime_iff_not_dvd.mpr
  intro h
  obtain ⟨s,hs,hd⟩ :=
    (IsLocalization.toLocalizationMap (planeOriginIdeal k).primeCompl
      (planeOriginRing k)).map_dvd_map.mp h
  rcases (MvPolynomial.X_prime (R := k) (i := (0 : Fin 2))).dvd_or_dvd hd with ha | hb
  · have hx : (MvPolynomial.X (0 : Fin 2) : planeCoordinateRing k) ∈ planeOriginIdeal k := by
      simp [planeOriginIdeal, RingHom.mem_ker]
    obtain ⟨a,rfl⟩ := ha
    exact hs ((planeOriginIdeal k).mul_mem_right a hx)
  · exact (by decide : (0 : Fin 2) ≠ 1) (MvPolynomial.X_dvd_X.mp hb)

noncomputable instance planeOriginRing_gcd : GCDMonoid (planeOriginRing k) :=
  UniqueFactorizationMonoid.toGCDMonoid _

example : IsNoetherianRing (planeOriginRing k) := inferInstance
example : IsLocalRing (planeOriginRing k) := inferInstance

end

section PowerCharts
variable {R K ι : Type*} [CommRing R] [Field K] [Algebra R K]

lemma linearEquiv_map_base_smul (P : (ι → K) ≃ₗ[K] (ι → K)) (a : R) (v : ι → K) :
    P (a • v) = a • P v :=
  (P.restrictScalars R).map_smul a v

lemma powerLocalization_idem (x : R) (L : Submodule R (ι → K)) :
    powerLocalization x (powerLocalization x L) = powerLocalization x L := by
  apply le_antisymm
  · rintro v ⟨n,m,h⟩
    exact ⟨m+n, by simpa only [pow_add, mul_smul] using h⟩
  · exact le_powerLocalization _ _

lemma powerLocalization_equiv_map (x : R) (L : Submodule R (ι → K))
    (P : (ι → K) ≃ₗ[K] (ι → K)) :
    powerLocalization x (L.map (P.toLinearMap.restrictScalars R)) =
      (powerLocalization x L).map (P.toLinearMap.restrictScalars R) := by
  apply le_antisymm
  · rintro v ⟨n,w,hw,he⟩
    refine ⟨P.symm v, ⟨n, ?_⟩, P.apply_symm_apply v⟩
    have h : w = x^n • P.symm v := by
      apply P.injective
      change P w = x^n • v at he
      simpa only [linearEquiv_map_base_smul, P.apply_symm_apply] using he
    exact h ▸ hw
  · rintro v ⟨w,⟨n,hn⟩,rfl⟩
    refine ⟨n,x^n • w,hn,?_⟩
    exact (P.restrictScalars R).map_smul _ _

end PowerCharts

section
variable {R K ι : Type*} [CommRing R] [Field K] [Algebra R K]

 
theorem gluedLattice_xChart (x y : R) (P : (ι → K) ≃ₗ[K] (ι → K))
    (d : ℕ) (hP : ∀ v ∈ coordinateLattice (R := R),
      (x*y)^d • P.symm v ∈ coordinateLattice (R := R)) :
    powerLocalization x (gluedLattice x y P) = powerLocalization x coordinateLattice := by
  apply le_antisymm
  · exact (powerLocalization_mono x inf_le_left).trans (le_of_eq (powerLocalization_idem x _))
  · rintro v hv
    obtain ⟨n,hn⟩ := hv
    refine ⟨d+n, ?_⟩
    change x^(d+n) • v ∈ powerLocalization x coordinateLattice ∧
      x^(d+n) • v ∈ (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R)
    constructor
    · exact ⟨0, by simpa only [pow_zero, one_smul, pow_add, mul_smul] using
        (coordinateLattice (R := R)).smul_mem (x^d) hn⟩
    · refine ⟨x^(d+n) • P.symm v, ⟨d, ?_⟩, ?_⟩
      · have h := hP (x^n • v) hn
        rw [linearEquiv_map_base_smul, mul_pow, mul_smul,
          smul_comm (y^d), ← mul_smul, ← pow_add] at h
        simpa only [smul_comm (y^d)] using h
      · change P (x^(d+n) • P.symm v) = x^(d+n) • v
        rw [linearEquiv_map_base_smul, P.apply_symm_apply]

 
theorem gluedLattice_yChart (x y : R) (P : (ι → K) ≃ₗ[K] (ι → K))
    (d : ℕ) (hP : ∀ v ∈ coordinateLattice (R := R),
      (x*y)^d • P v ∈ coordinateLattice (R := R)) :
    powerLocalization y (gluedLattice x y P) =
      (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R) := by
  apply le_antisymm
  · refine (powerLocalization_mono y inf_le_right).trans ?_
    rw [powerLocalization_equiv_map, powerLocalization_idem]
  · rintro v ⟨w,⟨n,hn⟩,rfl⟩
    refine ⟨d+n, ?_⟩
    change y^(d+n) • P w ∈ powerLocalization x coordinateLattice ∧
      y^(d+n) • P w ∈ (powerLocalization y coordinateLattice).map (P.toLinearMap.restrictScalars R)
    constructor
    · refine ⟨d, ?_⟩
      have h := hP (y^n • w) hn
      rw [linearEquiv_map_base_smul, mul_pow, mul_smul,
        ← mul_smul (y^d), ← pow_add] at h
      exact h
    · refine ⟨y^(d+n) • w, ⟨0, ?_⟩, ?_⟩
      · simpa only [pow_zero, one_smul, pow_add, mul_smul] using
          (coordinateLattice (R := R)).smul_mem (y^d) hn
      · exact (P.restrictScalars R).map_smul _ _

end

section

variable {k ι : Type*} [Field k] [Infinite k] [Fintype ι] [DecidableEq ι]
variable (P : Matrix ι ι (Polynomial k))
    (h0 : polynomialMatrixEval P (0 : k) = 1)
    (hadd : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)

abbrev planeOriginFractionField := FractionRing (planeCoordinateRing k)

instance planeOriginFraction_tower :
    IsScalarTower k (planeOriginRing k) (planeOriginFractionField (k := k)) :=
  IsScalarTower.to₁₃₄ k (planeCoordinateRing k) (planeOriginRing k)
    (planeOriginFractionField (k := k))

instance planeOriginFraction_isFractionRing :
    IsFractionRing (planeOriginRing k) (planeOriginFractionField (k := k)) :=
  IsFractionRing.isFractionRing_of_isLocalization (planeOriginIdeal k).primeCompl
    (planeOriginRing k) (planeOriginFractionField (k := k))
    (planeOriginIdeal k).primeCompl_le_nonZeroDivisors

noncomputable def planeStalkTransition :
    (ι → planeOriginFractionField (k := k)) ≃ₗ[planeOriginFractionField (k := k)]
      (ι → planeOriginFractionField (k := k)) :=
  polynomialActionEquiv P h0 hadd
    (-(algebraMap (planeOriginRing k) (planeOriginFractionField (k := k))
      (planeOriginCoordinate k 0 * planeOriginCoordinate k 1))⁻¹)

 

noncomputable def planeAssociatedLattice :
    Submodule (planeOriginRing k) (ι → planeOriginFractionField (k := k)) :=
  gluedLattice (planeOriginCoordinate k 0) (planeOriginCoordinate k 1)
    (planeStalkTransition P h0 hadd)

omit [Infinite k] in
lemma planeOrigin_product_ne_zero :
    algebraMap (planeOriginRing k) (planeOriginFractionField (k := k))
      (planeOriginCoordinate k 0 * planeOriginCoordinate k 1) ≠ 0 := by
  have h := FaithfulSMul.algebraMap_injective (planeOriginRing k)
    (planeOriginFractionField (k := k))
  exact fun hz => (mul_ne_zero (planeOriginCoordinate_ne_zero k 0)
    (planeOriginCoordinate_ne_zero k 1)) (h (hz.trans (map_zero _).symm))

lemma planeStalkTransition_denominator (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    ∀ v ∈ coordinateLattice (R := planeOriginRing k),
      (planeOriginCoordinate k 0 * planeOriginCoordinate k 1)^d •
        planeStalkTransition P h0 hadd v ∈ coordinateLattice (R := planeOriginRing k) :=
  polynomialAction_denominator P h0 hadd _ planeOrigin_product_ne_zero d hd

lemma planeStalkTransition_symm_denominator (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    ∀ v ∈ coordinateLattice (R := planeOriginRing k),
      (planeOriginCoordinate k 0 * planeOriginCoordinate k 1)^d •
        (planeStalkTransition P h0 hadd).symm v ∈ coordinateLattice (R := planeOriginRing k) := by
  have h := polynomialAction_fraction_denominator (R := planeOriginRing k)
    (K := planeOriginFractionField (k := k)) P h0 hadd 1 _ planeOrigin_product_ne_zero d hd
  simpa only [planeStalkTransition, polynomialActionEquiv_symm, neg_neg,
    map_one, one_mul] using h

 

theorem planeAssociatedLattice_finite_free (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    Module.Finite (planeOriginRing k) (planeAssociatedLattice P h0 hadd) ∧
      Module.Free (planeOriginRing k) (planeAssociatedLattice P h0 hadd) := by
  constructor
  · exact gluedLattice_finite _ _ (planeOriginCoordinate_ne_zero k 0)
      (planeOriginCoordinates_relPrime k) _ d (planeStalkTransition_denominator P h0 hadd d hd)
  · exact gluedLattice_free _ _ (planeOriginCoordinate_ne_zero k 0)
      (planeOriginCoordinate_ne_zero k 1) (planeOriginCoordinates_relPrime k)
      (planeOrigin_maximalIdeal k) _ d (planeStalkTransition_denominator P h0 hadd d hd)

theorem planeAssociatedLattice_xChart (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    powerLocalization (planeOriginCoordinate k 0) (planeAssociatedLattice P h0 hadd) =
      powerLocalization (planeOriginCoordinate k 0) coordinateLattice :=
  gluedLattice_xChart _ _ _ d (planeStalkTransition_symm_denominator P h0 hadd d hd)

theorem planeAssociatedLattice_yChart (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d) :
    powerLocalization (planeOriginCoordinate k 1) (planeAssociatedLattice P h0 hadd) =
      (powerLocalization (planeOriginCoordinate k 1) coordinateLattice).map
        ((planeStalkTransition P h0 hadd).toLinearMap.restrictScalars (planeOriginRing k)) :=
  gluedLattice_yChart _ _ _ d (planeStalkTransition_denominator P h0 hadd d hd)

end

variable (k : Type*) [Field k] [Infinite k]

abbrev planeOverlapRing := Localization.Away
  ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1)

omit [Infinite k] in
lemma planeTorusEvaluation_product_isUnit :
    IsUnit (planeTorusEvaluation k
      ((MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1)) := by
  rw [map_mul]
  exact (planeTorusEvaluation_X_isUnit k 0).mul (planeTorusEvaluation_X_isUnit k 1)

noncomputable def planeOverlapEvaluation :
    planeOverlapRing k →ₐ[k] (planeTorusPoints k → k) :=
  IsLocalization.Away.liftAlgHom _ (planeTorusEvaluation_product_isUnit k)

omit [Infinite k] in
lemma planeOverlapEvaluation_algebraMap (P : MvPolynomial (Fin 2) k) :
    planeOverlapEvaluation k (algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k) P) =
      planeTorusEvaluation k P :=
  IsLocalization.Away.lift_eq _ (planeTorusEvaluation_product_isUnit k) _

theorem planeOverlapEvaluation_injective :
    Function.Injective (planeOverlapEvaluation k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (R := MvPolynomial (Fin 2) k) (S := planeOverlapRing k)
    (Submonoid.powers (MvPolynomial.X 0 * MvPolynomial.X 1))
    (planeOverlapEvaluation k).toRingHom).mpr
  intro P Q
  constructor
  · exact congrArg (planeOverlapEvaluation k)
  · intro h
    have h' : planeTorusEvaluation k P = planeTorusEvaluation k Q := by
      simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        planeOverlapEvaluation_algebraMap] using h
    exact congrArg (algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k))
      (planeTorusEvaluation_injective k h')

omit [Infinite k] in
lemma planeOverlapCoordinate_isUnit (i : Fin 2) :
    IsUnit (algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k) (MvPolynomial.X i)) := by
  apply IsLocalization.Away.isUnit_of_dvd
    (x := (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) * MvPolynomial.X 1)
  fin_cases i
  · exact dvd_mul_right _ _
  · exact dvd_mul_left _ _

noncomputable def planeChartToOverlap (i : Fin 2) :
    planeCoordinateChart k i →ₐ[k] planeOverlapRing k :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X i : MvPolynomial (Fin 2) k)
    (f := IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) (planeOverlapRing k))
    (planeOverlapCoordinate_isUnit k i)

omit [Infinite k] in
lemma planeChartToOverlap_algebraMap (i : Fin 2) (P : MvPolynomial (Fin 2) k) :
    planeChartToOverlap k i
      (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k i) P) =
      algebraMap (MvPolynomial (Fin 2) k) (planeOverlapRing k) P :=
  IsLocalization.Away.lift_eq _ (planeOverlapCoordinate_isUnit k i) _

omit [Infinite k] in
lemma planeChartToOverlap_evaluation (i : Fin 2) (f : planeCoordinateChart k i) :
    planeOverlapEvaluation k (planeChartToOverlap k i f) = planeChartEvaluation k i f := by
  have h : (planeOverlapEvaluation k).toRingHom.comp (planeChartToOverlap k i).toRingHom =
      (planeChartEvaluation k i).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) k))
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      planeChartToOverlap_algebraMap, planeOverlapEvaluation_algebraMap,
      planeChartEvaluation_algebraMap]
  exact RingHom.congr_fun h f

lemma planeChartToOverlap_injective (i : Fin 2) : Function.Injective (planeChartToOverlap k i) := by
  intro f h he
  apply planeChartEvaluation_injective k i
  rw [← planeChartToOverlap_evaluation, ← planeChartToOverlap_evaluation, he]

end FiberFunctorProof
end

end OAI
