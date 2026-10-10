import Mathlib
import PrimeNumberTheoremAnd.SiegelZeros.HadamardSupport

namespace OAI

namespace SiegelZeros

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

noncomputable def coneMap (p : Ideal (MvPolynomial σ K)) :
    MvPolynomial (Option σ) K →ₐ[K] Polynomial (MvPolynomial σ K ⧸ p) :=
  MvPolynomial.aeval (fun o : Option σ => o.elim Polynomial.X
    (fun i => Polynomial.C (Ideal.Quotient.mk p (X i)) * Polynomial.X))

noncomputable def coneIdeal (p : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial (Option σ) K) := RingHom.ker (coneMap p)

noncomputable def coneDehomogenize :
    MvPolynomial (Option σ) K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun o : Option σ => o.elim 1 X)

@[simp] theorem coneMap_X_none (p : Ideal (MvPolynomial σ K)) :
    coneMap p (X none) = Polynomial.X := by
  simp [coneMap]

@[simp] theorem coneMap_X_some (p : Ideal (MvPolynomial σ K)) (i : σ) :
    coneMap p (X (some i)) =
      Polynomial.C (Ideal.Quotient.mk p (X i)) * Polynomial.X := by
  simp [coneMap]

theorem coneIdeal_isPrime (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (coneIdeal p).IsPrime := RingHom.ker_isPrime (coneMap p)

theorem X_none_not_mem_coneIdeal (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    X none ∉ coneIdeal p := by
  simpa only [coneIdeal, RingHom.mem_ker, coneMap_X_none] using
    (Polynomial.X_ne_zero : (Polynomial.X : Polynomial (MvPolynomial σ K ⧸ p)) ≠ 0)

theorem eval_one_coneMap (p : Ideal (MvPolynomial σ K))
    (f : MvPolynomial (Option σ) K) :
    Polynomial.eval 1 (coneMap p f) = Ideal.Quotient.mk p (coneDehomogenize f) := by
  have h : ((Polynomial.aeval (1 : MvPolynomial σ K ⧸ p)).restrictScalars K).comp
      (coneMap p) = (Ideal.Quotient.mkₐ K p).comp coneDehomogenize := by
    ext i
    cases i <;> simp [coneMap, coneDehomogenize]
  exact congrArg (fun g => g f) h

theorem map_coneIdeal_dehomogenize_le (p : Ideal (MvPolynomial σ K)) :
    Ideal.map coneDehomogenize.toRingHom (coneIdeal p) ≤ p := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro f hf
  change coneDehomogenize f ∈ p
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← eval_one_coneMap]
  simpa only [Polynomial.eval_zero] using
    congrArg (Polynomial.eval 1) (show coneMap p f = 0 from hf)

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry.DegreeBezout

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

open Polynomial IsLocalRing

theorem polynomial_local_coefficient_prime_map
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    (p.map (Polynomial.C : A →+* Polynomial A)).map
      (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) =
    (maximalIdeal (Localization.AtPrime p)).map Polynomial.C := by
  rw [← (show p.map (algebraMap A (Localization.AtPrime p)) =
      maximalIdeal (Localization.AtPrime p) from Localization.AtPrime.map_eq_maximalIdeal),
    Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  simp

theorem polynomial_coefficient_denominators_disjoint
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Disjoint ((p.primeCompl.map Polynomial.C : Submonoid (Polynomial A)) : Set (Polynomial A))
      ((p.map Polynomial.C : Ideal (Polynomial A)) : Set (Polynomial A)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨a, ha, rfl⟩ h
  exact ha (by simpa using (Ideal.mem_map_C_iff.mp h) 0)

noncomputable def polynomialLocalCoefficientPolyEquiv
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime (p.map (Polynomial.C : A →+* Polynomial A)) ≃ₐ[Polynomial A]
      Localization.AtPrime ((maximalIdeal (Localization.AtPrime p)).map Polynomial.C) := by
  let M : Submonoid (Polynomial A) := p.primeCompl.map Polynomial.C
  let q : Ideal (Polynomial (Localization.AtPrime p)) :=
    (maximalIdeal (Localization.AtPrime p)).map Polynomial.C
  have ht := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
    (M := M) (Localization.AtPrime q) q
  have hq : q = (p.map Polynomial.C).map
      (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) :=
    (polynomial_local_coefficient_prime_map p).symm
  have he := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial (Localization.AtPrime p))
    (show (p.map Polynomial.C).IsPrime from inferInstance)
    (polynomial_coefficient_denominators_disjoint p)
  rw [← hq] at he
  change q.comap (algebraMap (Polynomial A) (Polynomial (Localization.AtPrime p))) =
    p.map Polynomial.C at he
  simp_rw [he] at ht
  exact IsLocalization.algEquiv (p.map Polynomial.C).primeCompl _ _

noncomputable def polynomialLocalCoefficientEquiv
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime (p.map (Polynomial.C : A →+* Polynomial A)) ≃ₐ[A]
      Localization.AtPrime ((maximalIdeal (Localization.AtPrime p)).map Polynomial.C) :=
  (polynomialLocalCoefficientPolyEquiv p).restrictScalars A

theorem polynomialLocalCoefficientEquiv_polynomial
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] (f : Polynomial A) :
    polynomialLocalCoefficientEquiv p
      (algebraMap (Polynomial A) (Localization.AtPrime (p.map Polynomial.C)) f) =
      algebraMap (Polynomial A)
        (Localization.AtPrime ((maximalIdeal (Localization.AtPrime p)).map Polynomial.C)) f :=
  (polynomialLocalCoefficientPolyEquiv p).commutes f

theorem polynomialLocalCoefficientEquiv_algebraMap
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] (a : A) :
    polynomialLocalCoefficientEquiv p
      (algebraMap A (Localization.AtPrime (p.map Polynomial.C)) a) =
      algebraMap A
        (Localization.AtPrime ((maximalIdeal (Localization.AtPrime p)).map Polynomial.C)) a :=
  (polynomialLocalCoefficientEquiv p).commutes a

end WeightedTorusJets.Geometry.DegreeBezout

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

noncomputable def conePolynomialMap :
    MvPolynomial (Option σ) K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  MvPolynomial.aeval (fun o : Option σ => o.elim Polynomial.X
    (fun i => Polynomial.C (X i) * Polynomial.X))

@[simp] theorem conePolynomialMap_X_none :
    conePolynomialMap (X (none : Option σ) : MvPolynomial (Option σ) K) = Polynomial.X := by
  simp [conePolynomialMap]

@[simp] theorem conePolynomialMap_X_some (i : σ) :
    conePolynomialMap (X (some i) : MvPolynomial (Option σ) K) =
      Polynomial.C (X i) * Polynomial.X := by
  simp [conePolynomialMap]

local notation "𝒜" => MvPolynomial σ K
local notation "𝒮" => MvPolynomial (Option σ) K
local notation "𝒰" => Localization.Away (X (none : Option σ) : 𝒮)
local notation "𝒱" => Localization.Away (Polynomial.X : Polynomial 𝒜)

private noncomputable def coneAwayForward : 𝒰 →ₐ[K] 𝒱 :=
  IsLocalization.Away.liftAlgHom (X none)
    (f := (IsScalarTower.toAlgHom K (Polynomial 𝒜) 𝒱).comp conePolynomialMap) (by
      change IsUnit (algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap (X none)))
      rw [conePolynomialMap_X_none]
      exact IsLocalization.Away.algebraMap_isUnit (S := 𝒱) (Polynomial.X : Polynomial 𝒜))

private noncomputable def coneAwayInverseCoefficients : 𝒜 →ₐ[K] 𝒰 :=
  MvPolynomial.aeval (fun i => algebraMap 𝒮 𝒰 (X (some i)) *
    IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮))

private noncomputable def coneAwayBackward : 𝒱 →ₐ[K] 𝒰 :=
  IsLocalization.Away.liftAlgHom Polynomial.X
    (f := Polynomial.aevalTower coneAwayInverseCoefficients (algebraMap 𝒮 𝒰 (X none))) (by
      rw [Polynomial.aevalTower_X]
      exact IsLocalization.Away.algebraMap_isUnit (S := 𝒰) (X (none : Option σ) : 𝒮))

private theorem coneAwayForward_algebraMap (a : 𝒮) :
    coneAwayForward (algebraMap 𝒮 𝒰 a) = algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap a) :=
  by simp [coneAwayForward]

private theorem coneAwayBackward_algebraMap (a : Polynomial 𝒜) :
    coneAwayBackward (algebraMap (Polynomial 𝒜) 𝒱 a) =
      Polynomial.aevalTower coneAwayInverseCoefficients (algebraMap 𝒮 𝒰 (X none)) a :=
  by simp [coneAwayBackward]

private theorem coneAwayForward_invSelf :
    coneAwayForward (IsLocalization.Away.invSelf (X (none : Option σ) : 𝒮) : 𝒰) =
      (IsLocalization.Away.invSelf (Polynomial.X : Polynomial 𝒜) : 𝒱) := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := 𝒱)
    (Polynomial.X : Polynomial 𝒜)).mul_left_cancel
  rw [IsLocalization.Away.mul_invSelf]
  have h := congrArg (coneAwayForward : 𝒰 →ₐ[K] 𝒱)
    (IsLocalization.Away.mul_invSelf (S := 𝒰) (X (none : Option σ) : 𝒮))
  rw [map_mul, map_one, coneAwayForward_algebraMap, conePolynomialMap_X_none] at h
  exact h

private theorem coneAwayForward_comp_backward :
    (coneAwayForward : 𝒰 →ₐ[K] 𝒱).comp coneAwayBackward = AlgHom.id K 𝒱 := by
  apply IsLocalization.algHom_ext (Submonoid.powers (Polynomial.X : Polynomial 𝒜))
  apply Polynomial.algHom_ext'
  · ext i
    change coneAwayForward (coneAwayBackward
      (algebraMap (Polynomial 𝒜) 𝒱 (Polynomial.C (X i)))) =
        algebraMap (Polynomial 𝒜) 𝒱 (Polynomial.C (X i))
    rw [coneAwayBackward_algebraMap, Polynomial.aevalTower_C]
    rw [show coneAwayInverseCoefficients (X i) = algebraMap 𝒮 𝒰 (X (some i)) *
      IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮) from
        MvPolynomial.aeval_X _ _]
    rw [map_mul, coneAwayForward_algebraMap, coneAwayForward_invSelf,
      conePolynomialMap_X_some, map_mul, mul_assoc,
      IsLocalization.Away.mul_invSelf, mul_one]
  · change coneAwayForward (coneAwayBackward (algebraMap (Polynomial 𝒜) 𝒱 Polynomial.X)) =
      algebraMap (Polynomial 𝒜) 𝒱 Polynomial.X
    rw [coneAwayBackward_algebraMap, Polynomial.aevalTower_X,
      coneAwayForward_algebraMap, conePolynomialMap_X_none]

private theorem coneAwayBackward_comp_forward :
    (coneAwayBackward : 𝒱 →ₐ[K] 𝒰).comp coneAwayForward = AlgHom.id K 𝒰 := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X (none : Option σ) : 𝒮))
  ext i
  change coneAwayBackward (coneAwayForward (algebraMap 𝒮 𝒰 (X i))) = algebraMap 𝒮 𝒰 (X i)
  rw [coneAwayForward_algebraMap]
  cases i with
  | none =>
    rw [conePolynomialMap_X_none, coneAwayBackward_algebraMap, Polynomial.aevalTower_X]
  | some i =>
    rw [conePolynomialMap_X_some, coneAwayBackward_algebraMap, map_mul,
      Polynomial.aevalTower_C, Polynomial.aevalTower_X]
    rw [show coneAwayInverseCoefficients (X i) = algebraMap 𝒮 𝒰 (X (some i)) *
      IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮) from
        MvPolynomial.aeval_X _ _]
    rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (S := 𝒰) (X (none : Option σ) : 𝒮)),
      IsLocalization.Away.mul_invSelf, mul_one]

noncomputable def coneAwayEquiv : 𝒰 ≃ₐ[K] 𝒱 :=
  AlgEquiv.ofAlgHom coneAwayForward coneAwayBackward
    coneAwayForward_comp_backward coneAwayBackward_comp_forward

@[simp] theorem coneAwayEquiv_algebraMap (a : 𝒮) :
    coneAwayEquiv (algebraMap 𝒮 𝒰 a) = algebraMap (Polynomial 𝒜) 𝒱 (conePolynomialMap a) :=
  coneAwayForward_algebraMap a

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

theorem coneIdeal_eq_comap_polynomial (p : Ideal (MvPolynomial σ K)) :
    coneIdeal p = (p.map Polynomial.C).comap conePolynomialMap := by
  have h : (Polynomial.mapRingHom (Ideal.Quotient.mk p)).comp
      conePolynomialMap.toRingHom = (coneMap p).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap, conePolynomialMap]
      rfl
    · intro i
      cases i <;> simp [coneMap, conePolynomialMap]
  calc
    coneIdeal p = RingHom.ker ((Polynomial.mapRingHom (Ideal.Quotient.mk p)).comp
        conePolynomialMap.toRingHom) := by rw [h]; rfl
    _ = (RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk p))).comap
        conePolynomialMap := rfl
    _ = _ := by rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]

private theorem polynomial_X_powers_disjoint (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Disjoint ((Submonoid.powers (Polynomial.X : Polynomial (MvPolynomial σ K))) :
      Set (Polynomial (MvPolynomial σ K)))
      ((p.map Polynomial.C : Ideal (Polynomial (MvPolynomial σ K))) :
        Set (Polynomial (MvPolynomial σ K))) := by
  apply (Ideal.disjoint_powers_iff_notMem_of_isPrime Polynomial.X).mpr
  intro h
  have h1 : (1 : MvPolynomial σ K) ∈ p := by simpa using (Ideal.mem_map_C_iff.mp h) 1
  exact (show p.IsPrime from inferInstance).ne_top (p.eq_top_of_isUnit_mem h1 isUnit_one)

theorem polynomialAwayPrime_isPrime (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    ((p.map Polynomial.C).map (algebraMap (Polynomial (MvPolynomial σ K))
      (Localization.Away (Polynomial.X : Polynomial (MvPolynomial σ K))))).IsPrime :=
  IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers Polynomial.X) _ _
    inferInstance (polynomial_X_powers_disjoint p)

attribute [local instance] coneIdeal_isPrime polynomialAwayPrime_isPrime

noncomputable def conePolynomialLocalEquiv (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime (coneIdeal p) ≃ₐ[K] Localization.AtPrime (p.map Polynomial.C) := by
  let A := MvPolynomial σ K
  let S := MvPolynomial (Option σ) K
  let U := Localization.Away (X (none : Option σ) : S)
  let V := Localization.Away (Polynomial.X : Polynomial A)
  let q : Ideal (Polynomial A) := p.map Polynomial.C
  have hd := polynomial_X_powers_disjoint p
  let q' := q.map (algebraMap (Polynomial A) V)
  have hq' : q'.comap (algebraMap (Polynomial A) V) = q :=
    IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers (Polynomial.X : Polynomial A)) V inferInstance hd
  let e : U ≃ₐ[K] V := coneAwayEquiv
  let p' := q'.comap e.toRingHom
  have hp' : p'.comap (algebraMap S U) = coneIdeal p := by
    change q'.comap (e.toRingHom.comp (algebraMap S U)) = _
    have he : e.toRingHom.comp (algebraMap S U) =
        (algebraMap (Polynomial A) V).comp conePolynomialMap.toRingHom := by
      apply RingHom.ext
      intro f
      exact coneAwayEquiv_algebraMap f
    rw [he, ← Ideal.comap_comap, hq']
    exact (coneIdeal_eq_comap_polynomial p).symm
  let eS : Localization.AtPrime (coneIdeal p) ≃ₐ[S] Localization.AtPrime p' := by
    let : IsLocalization (coneIdeal p).primeCompl (Localization.AtPrime p') := by
      have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers (X (none : Option σ) : S)) (Localization.AtPrime p') p'
      change IsLocalization (p'.comap (algebraMap S U)).primeCompl (Localization.AtPrime p') at h
      simpa only [hp'] using h
    exact IsLocalization.algEquiv (coneIdeal p).primeCompl _ _
  let eB : Localization.AtPrime q ≃ₐ[Polynomial A] Localization.AtPrime q' := by
    let : IsLocalization q.primeCompl (Localization.AtPrime q') := by
      have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers (Polynomial.X : Polynomial A)) (Localization.AtPrime q') q'
      simpa only [hq'] using h
    exact IsLocalization.algEquiv q.primeCompl _ _
  exact ((eS.restrictScalars K).trans
    (Localization.localAlgEquiv p' q' e rfl)).trans (eB.restrictScalars K).symm

theorem conePolynomialLocalEquiv_algebraMap (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : MvPolynomial (Option σ) K) :
    conePolynomialLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f) =
      algebraMap (Polynomial (MvPolynomial σ K))
        (Localization.AtPrime (p.map Polynomial.C)) (conePolynomialMap f) := by
  dsimp only [conePolynomialLocalEquiv, AlgEquiv.trans_apply]
  rw [AlgEquiv.symm_apply_eq]
  simp only [AlgEquiv.restrictScalars_apply, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (Option σ) K)
    (Localization.Away (X (none : Option σ) : MvPolynomial (Option σ) K))]
  rw [IsScalarTower.algebraMap_apply (Polynomial (MvPolynomial σ K))
    (Localization.Away (Polynomial.X : Polynomial (MvPolynomial σ K)))]
  exact (Localization.localRingHom_to_map _ _ coneAwayEquiv.toRingHom rfl _).trans
    (congrArg _ (coneAwayEquiv_algebraMap f))

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

open MvPolynomial

variable {K σ : Type*} [CommRing K]

attribute [local instance] coneIdeal_isPrime Polynomial.algebra Polynomial.isLocalization

noncomputable def coneLocalEquiv (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    Localization.AtPrime (coneIdeal p) ≃ₐ[K]
      Localization.AtPrime
        ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C) :=
  (conePolynomialLocalEquiv p).trans
    ((DegreeBezout.polynomialLocalCoefficientPolyEquiv p).restrictScalars K)

theorem coneLocalEquiv_algebraMap (p : Ideal (MvPolynomial σ K)) [p.IsPrime]
    (f : MvPolynomial (Option σ) K) :
    coneLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f) =
      algebraMap (Polynomial (Localization.AtPrime p))
        (Localization.AtPrime
          ((IsLocalRing.maximalIdeal (Localization.AtPrime p)).map Polynomial.C))
        (Polynomial.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime p))
          (conePolynomialMap f)) := by
  change DegreeBezout.polynomialLocalCoefficientPolyEquiv p
    (conePolynomialLocalEquiv p
      (algebraMap (MvPolynomial (Option σ) K) (Localization.AtPrime (coneIdeal p)) f)) = _
  rw [conePolynomialLocalEquiv_algebraMap, AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (Polynomial (MvPolynomial σ K))
    (Polynomial (Localization.AtPrime p))]
  rfl

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem polynomial_height_map_C (p : Ideal A) [p.IsPrime] :
    (p.map (Polynomial.C : A →+* Polynomial A)).height = p.height := by
  have : (p.map (Polynomial.C : A →+* Polynomial A)).LiesOver p := by
    constructor
    ext r
    change r ∈ p ↔ Polynomial.C r ∈ p.map Polynomial.C
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      simpa only [Polynomial.coeff_C_zero] using (Ideal.mem_map_C_iff.mp h) 0
  simp [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p]

theorem local_polynomial_prime_ringKrullDim (p : Ideal A) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime (p.map (Polynomial.C : A →+* Polynomial A))) =
      ringKrullDim (Localization.AtPrime p) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (p.map Polynomial.C)
      (Localization.AtPrime (p.map Polynomial.C)),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    polynomial_height_map_C]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

variable {K σ : Type*} [CommRing K] [IsNoetherianRing K] [Finite σ]

theorem coneIdeal_height (p : Ideal (MvPolynomial σ K)) [p.IsPrime] :
    (coneIdeal p).height = p.height := by
  let : (coneIdeal p).IsPrime := coneIdeal_isPrime p
  have h := ringKrullDim_eq_of_ringEquiv (conePolynomialLocalEquiv p).toRingEquiv
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (coneIdeal p)
      (Localization.AtPrime (coneIdeal p)),
    IsLocalization.AtPrime.ringKrullDim_eq_height (p.map Polynomial.C)
      (Localization.AtPrime (p.map Polynomial.C)), polynomial_height_map_C] at h
  exact WithBot.coe_eq_coe.mp h

end WeightedTorusJets.Geometry



end SiegelZeros

end OAI
