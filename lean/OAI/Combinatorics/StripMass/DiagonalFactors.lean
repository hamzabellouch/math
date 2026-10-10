import Mathlib
import OAI.Combinatorics.StripMass.LastRow
import OAI.Combinatorics.StripMass.PfaffianSupport

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

def separateCosine {n : ℕ} (i : Fin n) :
    CosineRing n ≃ₐ[ℂ] Polynomial (MvPolynomial {k : Fin n // k ≠ i} ℂ) :=
  (MvPolynomial.renameEquiv ℂ (Equiv.optionSubtypeNe i).symm).trans
    (MvPolynomial.optionEquivLeft ℂ _)

@[simp] theorem separateCosine_C {n : ℕ} (i : Fin n) (z : ℂ) :
    separateCosine i (MvPolynomial.C z) = Polynomial.C (MvPolynomial.C z) := by
  simp [separateCosine]

@[simp] theorem separateCosine_self {n : ℕ} (i : Fin n) :
    separateCosine i (MvPolynomial.X i) = Polynomial.X := by
  simp [separateCosine]

@[simp] theorem separateCosine_other {n : ℕ} (i j : Fin n) (h : j ≠ i) :
    separateCosine i (MvPolynomial.X j) = Polynomial.C (MvPolynomial.X ⟨j,h⟩) := by
  simp [separateCosine, Equiv.optionSubtypeNe_symm_of_ne h]

def cosineDiagonalEval {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    CosineRing n →+* MvPolynomial {k : Fin n // k ≠ i} ℂ :=
  (Polynomial.evalRingHom (MvPolynomial.X ⟨j,hji⟩)).comp (separateCosine i).toRingHom

@[simp] theorem cosineDiagonalEval_C {n : ℕ} (i j : Fin n) (hji : j ≠ i) (z : ℂ) :
    cosineDiagonalEval i j hji (MvPolynomial.C z) = MvPolynomial.C z := by
  simp [cosineDiagonalEval]

@[simp] theorem cosineDiagonalEval_self {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    cosineDiagonalEval i j hji (MvPolynomial.X i) = MvPolynomial.X ⟨j,hji⟩ := by
  simp [cosineDiagonalEval]

@[simp] theorem cosineDiagonalEval_other {n : ℕ} (i j k : Fin n)
    (hji : j ≠ i) (hki : k ≠ i) :
    cosineDiagonalEval i j hji (MvPolynomial.X k) = MvPolynomial.X ⟨k,hki⟩ := by
  simp [cosineDiagonalEval, hki]

theorem cosineDiagonalEval_swap {n : ℕ} (i j : Fin n) (hji : j ≠ i) :
    (cosineDiagonalEval i j hji).comp (MvPolynomial.rename (Equiv.swap i j)).toRingHom =
      cosineDiagonalEval i j hji := by
  ext k
  · simp
  · by_cases hki : k = i
    · subst k; simp [hji]
    · by_cases hkj : k = j
      · subst k; simp [hji]
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki]

theorem prime_cosine_difference {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Prime (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) := by
  apply (MulEquiv.prime_iff (separateCosine i)).mp
  simpa [map_sub, hij.symm] using
    Polynomial.prime_X_sub_C (MvPolynomial.X (⟨j,hij.symm⟩ : {k : Fin n // k ≠ i}) :
      MvPolynomial {k : Fin n // k ≠ i} ℂ)

 
theorem cosine_difference_dvd_of_swap {n : ℕ} (p : CosineRing n)
    (i j : Fin n) (hij : i ≠ j)
    (hp : MvPolynomial.rename (Equiv.swap i j) p = -p) :
    (MvPolynomial.X i - MvPolynomial.X j) ∣ p := by
  let E := cosineDiagonalEval i j hij.symm
  have he : E (MvPolynomial.rename (Equiv.swap i j) p) = E p :=
    congrArg (fun f : CosineRing n →+* _ => f p) (cosineDiagonalEval_swap i j hij.symm)
  have hz : E p = 0 := by
    rw [hp, map_neg] at he
    have hh : (2 : MvPolynomial {k : Fin n // k ≠ i} ℂ) * E p = 0 := by
      linear_combination -he
    exact (mul_eq_zero.mp hh).resolve_left (by norm_num)
  have hd : Polynomial.X - Polynomial.C (MvPolynomial.X ⟨j,hij.symm⟩) ∣
      separateCosine i p := Polynomial.dvd_iff_isRoot.mpr hz
  obtain ⟨q,hq⟩ := hd
  refine ⟨(separateCosine i).symm q, ?_⟩
  apply (separateCosine i).injective
  simpa [map_mul, map_sub, hij.symm] using hq

 

theorem cosine_differences_relPrime {n : ℕ} (e f : UpperPair n) (hef : e ≠ f) :
    IsRelPrime (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n)
      (MvPolynomial.X f.val.1 - MvPolynomial.X f.val.2) := by
  apply (prime_cosine_difference e.val.1 e.val.2 (ne_of_lt e.property)).irreducible.isRelPrime_iff_not_dvd.mpr
  intro hdiv
  let c : Fin n → Fin n := fun k => if k = e.val.1 then e.val.2 else k
  have hc : MvPolynomial.rename c
      (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n) = 0 := by
    simp [c, ne_of_gt e.property]
  have hd := map_dvd (MvPolynomial.rename c : CosineRing n →ₐ[ℂ] CosineRing n) hdiv
  rw [hc, zero_dvd_iff] at hd
  have heq : c f.val.1 = c f.val.2 := by
    apply MvPolynomial.X_injective (R := ℂ)
    exact sub_eq_zero.mp (by simpa only [map_sub, MvPolynomial.rename_X] using hd)
  have he := e.property
  have hf := f.property
  apply hef
  apply Subtype.ext
  dsimp [c] at heq
  split_ifs at heq with h₁ h₂ h₂
  · exact False.elim (ne_of_lt hf (h₁.trans h₂.symm))
  · exact Prod.ext h₁.symm heq
  · exact False.elim (by omega)
  · exact False.elim (ne_of_lt hf heq)

 
theorem scalarNumerator_vandermonde_dvd (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) :
    (∏ e : UpperPair n, (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n)) ∣
      scalarNumerator n dd rr := by
  let : UniqueFactorizationMonoid (CosineRing n) := MvPolynomial.uniqueFactorizationMonoid (Fin n)
  let : DecompositionMonoid (CosineRing n) := UniqueFactorizationMonoid.instDecompositionMonoid
  apply Fintype.prod_dvd_of_isRelPrime
    (s := fun e : UpperPair n => (MvPolynomial.X e.val.1 - MvPolynomial.X e.val.2 : CosineRing n))
    (fun e f hef => cosine_differences_relPrime e f hef)
  intro e
  apply cosine_difference_dvd_of_swap _ _ _ (ne_of_lt e.property)
  rw [scalarNumerator_rename dd rr hdd, Equiv.Perm.sign_swap (ne_of_lt e.property)]
  simp


 

 


 
def sourceVandermonde {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) : R :=
  ∏ e : UpperPair n, (a e.val.1 - a e.val.2)

theorem sourceVandermonde_ne_zero {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
    (a : Fin n → R) (ha : Function.Injective a) : sourceVandermonde a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro e _
  exact sub_ne_zero.mpr (ha.ne (ne_of_lt e.property))

theorem sourceVandermonde_eq_det {R : Type*} [CommRing R] {n : ℕ} (a : Fin n → R) :
    sourceVandermonde a = Matrix.det (Matrix.vandermonde (fun i => -a i)) := by
  rw [Matrix.det_vandermonde, sourceVandermonde, prod_upperPair (fun i j => a i - a j)]
  simp only [neg_sub_neg]

theorem sourceVandermonde_reindex {R : Type*} [CommRing R] {n : ℕ}
    (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    sourceVandermonde (a ∘ σ) = (Equiv.Perm.sign σ : ℤ) * sourceVandermonde a := by
  rw [sourceVandermonde_eq_det, sourceVandermonde_eq_det]
  have hm : Matrix.vandermonde (fun i => -(a ∘ σ) i) =
      (Matrix.vandermonde (fun i => -a i)).submatrix σ id := by
    rfl
  rw [hm, Matrix.det_permute]

theorem map_sourceVandermonde {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (a : Fin n → R) :
    f (sourceVandermonde a) = sourceVandermonde (fun i => f (a i)) := by
  simp [sourceVandermonde, map_prod]

 

def scalarPolynomial (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) : CosineRing n :=
  Classical.choose (scalarNumerator_vandermonde_dvd n dd rr hdd)

theorem scalarNumerator_eq_vandermonde (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) :
    scalarNumerator n dd rr = sourceVandermonde MvPolynomial.X * scalarPolynomial n dd rr hdd :=
  Classical.choose_spec (scalarNumerator_vandermonde_dvd n dd rr hdd)

 

theorem scalarPolynomial_eval {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (a : Fin n → K)
    (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) =
      scalarNormalization (f dd) (f rr) a := by
  have h := scalarNumerator_eval_vandermonde f n dd rr a ha hD
  rw [scalarNumerator_eq_vandermonde n dd rr hdd, map_mul,
    map_sourceVandermonde] at h
  simp only [MvPolynomial.eval₂Hom_X'] at h
  rw [← prod_upperPair] at h
  exact mul_left_cancel₀ (sourceVandermonde_ne_zero a ha) h

 
theorem scalarPolynomial_rename {n : ℕ} (dd rr : ℂ) (hdd : dd ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename σ (scalarPolynomial n dd rr hdd) = scalarPolynomial n dd rr hdd := by
  have h := congrArg (MvPolynomial.rename σ) (scalarNumerator_eq_vandermonde n dd rr hdd)
  have hv : MvPolynomial.rename σ
      (sourceVandermonde (MvPolynomial.X : Fin n → CosineRing n)) =
      sourceVandermonde (MvPolynomial.X ∘ σ) := by
    simp [sourceVandermonde, map_prod]
  rw [scalarNumerator_rename dd rr hdd σ, map_mul, hv] at h
  rw [sourceVandermonde_reindex MvPolynomial.X σ,
    scalarNumerator_eq_vandermonde n dd rr hdd] at h
  have hs : (((Equiv.Perm.sign σ : ℤ) : CosineRing n)) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  apply mul_left_cancel₀ (mul_ne_zero hs
    (sourceVandermonde_ne_zero (MvPolynomial.X : Fin n → CosineRing n) MvPolynomial.X_injective))
  simpa only [mul_assoc] using h.symm

end

 

 

noncomputable section
open Finset
open scoped Classical

lemma scalarNormalization_quotient {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) :
    scalarNormalization dd rr a =
      (∏ e : UpperPair n,discriminant dd (a e.val.1) (a e.val.2)) /
        sourceVandermonde a * pfaffian (augmentedKernel dd rr a) := by
  rw [scalarNormalization,←prod_upperPair,Finset.prod_div_distrib]
  rfl

lemma scalarNormalization_reindex {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    scalarNormalization dd rr (a ∘ σ)=scalarNormalization dd rr a := by
  rw [scalarNormalization_quotient,scalarNormalization_quotient,
    sourceVandermonde_reindex,augmentedKernel_reindex,pfaffian_reindex,augmentedPerm_sign]
  have hp : (∏ e : UpperPair n, discriminant dd ((a ∘ σ) e.val.1) ((a ∘ σ) e.val.2))=
      ∏ e : UpperPair n, discriminant dd (a e.val.1) (a e.val.2) :=
    prod_upperPair_reindex (fun i j => discriminant dd (a i) (a j))
      (fun i j => discriminant_symm dd (a i) (a j)) σ
  rw [hp]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs,div_neg]

lemma map_pfaffian {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (M : Matrix (Fin n) (Fin n) K) :
    f (pfaffian M)=pfaffian (M.map f) := by
  simp only [pfaffian,map_mul,map_inv₀,map_pow,map_ofNat,map_natCast,map_sum,
    map_intCast,map_prod,Matrix.map_apply]

lemma map_augmentedKernel {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (dd rr : K) (a : Fin n → K) :
    (augmentedKernel dd rr a).map f=augmentedKernel (f dd) (f rr) (fun i => f (a i)) := by
  ext i j
  change f (augmentedKernel dd rr a i j)=_
  unfold augmentedKernel
  split_ifs <;> simp [discriminant,map_div₀,map_pow,map_ofNat]

lemma map_scalarNormalization {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (dd rr : K) (a : Fin n → K) :
    f (scalarNormalization dd rr a)=scalarNormalization (f dd) (f rr) (fun i => f (a i)) := by
  simp only [scalarNormalization,map_mul,map_pfaffian,map_augmentedKernel,map_prod,
    map_div₀,discriminant,map_sub,map_add,map_pow,map_ofNat]

lemma permSpectral_normalization {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    permSpectral σ (spectralNormalization n)=spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,permSpectral_const,permSpectral_spectralA]
  exact scalarNormalization_reindex (constF n d) (constF n rho) spectralA σ

end

 

 

noncomputable section
open scoped Classical

 

def insertExponent {n : ℕ} (i : Fin (n+1)) : (Fin n → ℤ) →+ (Fin (n+1) → ℤ) where
  toFun e := Fin.insertNth i 0 e
  map_zero' := by funext j; refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp
  map_add' e f := by funext j; refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp

lemma insertExponent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (insertExponent i) := by
  intro e f h
  funext j
  simpa [insertExponent] using congrFun h (i.succAbove j)

def insertLaurent {n : ℕ} (i : Fin (n+1)) : Laurent n →+* Laurent (n+1) :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (insertExponent i)

lemma insertLaurent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (insertLaurent i) :=
  AddMonoidAlgebra.mapDomain_injective (insertExponent_injective i)

def insertSpectral {n : ℕ} (i : Fin (n+1)) : SpectralField n →+* SpectralField (n+1) :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (insertLaurent i))
    ((IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))).comp
      (insertLaurent_injective i))

@[simp] lemma insertSpectral_evalLaurent {n : ℕ} (i : Fin (n+1)) (f : Laurent n) :
    insertSpectral i (evalLaurent f)=evalLaurent (insertLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma insertLaurent_monomial {n : ℕ} (i : Fin (n+1)) (e : Fin n → ℤ) (z : ℂ) :
    insertLaurent i (monomialL e z)=monomialL (Fin.insertNth i 0 e) z :=
  AddMonoidAlgebra.mapDomain_single

@[simp] lemma insertSpectral_const {n : ℕ} (i : Fin (n+1)) (z : ℂ) :
    insertSpectral i (constF n z)=constF (n+1) z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,insertSpectral_evalLaurent]
  change evalLaurent (insertLaurent i (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [insertLaurent_monomial]
  congr 2
  exact (insertExponent i).map_zero

@[simp] lemma insertSpectral_variable {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertSpectral i (variableF j)=variableF (i.succAbove j) := by
  change insertSpectral i (evalLaurent (monomialL (variableExponent j) 1))=_
  rw [insertSpectral_evalLaurent,insertLaurent_monomial]
  congr 2
  funext k
  refine Fin.succAboveCases i ?_ (fun l => ?_) k
  · simp [variableExponent]
  · simp [variableExponent,Pi.single_apply]

@[simp] lemma insertSpectral_torusSin {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusSin z)=torusSin (insertSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma insertSpectral_torusCos {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusCos z)=torusCos (insertSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma insertSpectral_torusL {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    insertSpectral i (torusL z)=torusL (insertSpectral i z) := by simp [torusL]

@[simp] lemma insertSpectral_torusWeights {n : ℕ} (i : Fin (n+1)) (z : SpectralField n) :
    (torusWeights z).map (insertSpectral i)=torusWeights (insertSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

@[simp] lemma insertSpectral_spectralWeights {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    (spectralWeights n j).map (insertSpectral i)=spectralWeights (n+1) (i.succAbove j) := by
  simp [spectralWeights,map_div₀]

@[simp] lemma insertSpectral_spectralA {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertSpectral i (spectralA j)=spectralA (i.succAbove j) := by simp [spectralA,map_div₀]

lemma insertSpectral_vacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing n) :
    insertSpectral i (normalizedVacuum (spectralWeights n) p)=
      normalizedVacuum (fun j => spectralWeights (n+1) (i.succAbove j)) p := by
  have h:=congrFun (normalizedVacuum_map (insertSpectral i) (spectralWeights n) (spectral_regular n)) p
  simpa using h

lemma insertSpectral_normalization {n : ℕ} (i : Fin (n+1)) :
    insertSpectral i (spectralNormalization n)=
      scalarNormalization (constF (n+1) d) (constF (n+1) rho) (fun j => spectralA (i.succAbove j)) := by
  simp only [spectralNormalization,map_scalarNormalization,insertSpectral_const,insertSpectral_spectralA]

end

 

 

noncomputable section
open scoped LaurentPolynomial

 
def peelExponent {n : ℕ} (i : Fin (n+1)) : (Fin (n+1) → ℤ) ≃+ (ℤ × (Fin n → ℤ)) where
  toFun e := (e i,Fin.removeNth i e)
  invFun p := Fin.insertNth i p.1 p.2
  left_inv e := by simp
  right_inv p := by simp
  map_add' e f := rfl

def peelLaurentEquiv {n : ℕ} (i : Fin (n+1)) :
    Laurent (n+1) ≃+* LaurentPolynomial (Laurent n) :=
  (AddMonoidAlgebra.mapDomainRingEquiv ℂ (peelExponent i)).trans
    AddMonoidAlgebra.curryRingEquiv

@[simp] lemma peelLaurentEquiv_monomial {n : ℕ} (i : Fin (n+1))
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    peelLaurentEquiv i (monomialL e z)=AddMonoidAlgebra.single (e i)
      (monomialL (Fin.removeNth i e) z) := by
  change AddMonoidAlgebra.curryRingEquiv
    (AddMonoidAlgebra.mapDomain (peelExponent i) (AddMonoidAlgebra.single e z))=_
  rw [AddMonoidAlgebra.mapDomain_single]
  exact AddMonoidAlgebra.curryRingEquiv_single _ _ _

 
def peelLaurent {n : ℕ} (i : Fin (n+1)) :
    Laurent (n+1) →+* LaurentPolynomial (SpectralField n) :=
  (AddMonoidAlgebra.mapRingHom ℤ (algebraMap (SpectralRing n) (SpectralField n))).comp
    (peelLaurentEquiv i).toRingHom

lemma peelLaurent_injective {n : ℕ} (i : Fin (n+1)) : Function.Injective (peelLaurent i) :=
  (AddMonoidAlgebra.map_injective _ (IsFractionRing.injective (SpectralRing n) (SpectralField n))).comp
    (peelLaurentEquiv i).injective

@[simp] lemma peelLaurent_monomial {n : ℕ} (i : Fin (n+1)) (e : Fin (n+1) → ℤ) (z : ℂ) :
    peelLaurent i (monomialL e z)=AddMonoidAlgebra.single (e i)
      (evalLaurent (monomialL (Fin.removeNth i e) z)) := by
  change AddMonoidAlgebra.mapRingHom ℤ _ (peelLaurentEquiv i (monomialL e z))=_
  rw [peelLaurentEquiv_monomial]
  exact AddMonoidAlgebra.mapRingHom_single _ _ _

lemma peelLaurent_insert {n : ℕ} (i : Fin (n+1)) (f : Laurent n) :
    peelLaurent i (insertLaurent i f)=LaurentPolynomial.C (evalLaurent f) := by
  have h : (peelLaurent i).comp (insertLaurent i)=
      LaurentPolynomial.C.comp (algebraMap (SpectralRing n) (SpectralField n)) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change peelLaurent i (insertLaurent i (monomialL _ _))=_
    all_goals
      rw [insertLaurent_monomial,peelLaurent_monomial]
      simp only [Fin.insertNth_apply_same,Fin.removeNth_insertNth]
      rfl
  exact DFunLike.congr_fun h f

lemma peelLaurent_variable {n : ℕ} (i : Fin (n+1)) :
    peelLaurent i (monomialL (variableExponent i) 1)=LaurentPolynomial.T 1 := by
  rw [peelLaurent_monomial]
  have h : Fin.removeNth i (variableExponent i)=0 := by
    funext j
    simp [Fin.removeNth,variableExponent,Fin.succAbove_ne]
  rw [h]
  have he : variableExponent i i=1 := by simp [variableExponent]
  rw [he,monomialL_zero_one,evalLaurent,map_one]
  rfl

instance peeledRingIsDomain (n : ℕ) : IsDomain (LaurentPolynomial (SpectralField n)) :=
  AddMonoidAlgebra.instIsDomainOfIsCancelAddOfUniqueSums

abbrev SingleSpectral (n : ℕ) := FractionRing (LaurentPolynomial (SpectralField n))

instance singleSpectralField (n : ℕ) : Field (SingleSpectral n) := FractionRing.field _

def peelSpectral {n : ℕ} (i : Fin (n+1)) : SpectralField (n+1) →+* SingleSpectral n :=
  IsFractionRing.lift (K := SpectralField (n+1))
    (g := (algebraMap (LaurentPolynomial (SpectralField n)) (SingleSpectral n)).comp (peelLaurent i))
    ((IsFractionRing.injective (LaurentPolynomial (SpectralField n)) (SingleSpectral n)).comp (peelLaurent_injective i))

@[simp] lemma peelSpectral_evalLaurent {n : ℕ} (i : Fin (n+1)) (f : Laurent (n+1)) :
    peelSpectral i (evalLaurent f)=
      algebraMap (LaurentPolynomial (SpectralField n)) (SingleSpectral n) (peelLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

def singleCoeff (n : ℕ) : SpectralField n →+* SingleSpectral n :=
  (algebraMap (LaurentPolynomial (SpectralField n)) (SingleSpectral n)).comp LaurentPolynomial.C

lemma peelSpectral_insert {n : ℕ} (i : Fin (n+1)) (x : SpectralField n) :
    peelSpectral i (insertSpectral i x)=singleCoeff n x := by
  have h : (peelSpectral i).comp (insertSpectral i)=singleCoeff n := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change peelSpectral i (insertSpectral i (evalLaurent f))=
      algebraMap (LaurentPolynomial (SpectralField n)) (SingleSpectral n)
        (LaurentPolynomial.C (evalLaurent f))
    rw [insertSpectral_evalLaurent,peelSpectral_evalLaurent,peelLaurent_insert]
  exact DFunLike.congr_fun h x

end

 

 

 

noncomputable section
open scoped LaurentPolynomial Classical

variable {K : Type*} [Field K]

def LaurentInterval (f : LaurentPolynomial K) (a b : ℤ) : Prop :=
  ∀ e, f.coeff e ≠ 0 → a ≤ e ∧ e ≤ b

lemma laurent_trunc_coeff (f : LaurentPolynomial K) (k : ℕ) :
    (LaurentPolynomial.trunc f).coeff k=f.coeff (k:ℤ) := rfl

lemma laurent_toLaurent_coeff (p : Polynomial K) (k : ℕ) :
    p.toLaurent.coeff (k:ℤ)=p.coeff k := by
  rw [LaurentPolynomial.coeff_toLaurent]
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective p.toFinsupp.coeff k

lemma laurent_toLaurent_negative (p : Polynomial K) (e : ℤ) (he : e<0) :
    p.toLaurent.coeff e=0 := by
  rw [LaurentPolynomial.coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨n,hn⟩
  have : (0:ℤ)≤n := Int.natCast_nonneg _
  change (n:ℤ)=e at hn
  omega

lemma laurent_toLaurent_trunc (f : LaurentPolynomial K)
    (h : ∀ e,e<0 → f.coeff e=0) :
    (LaurentPolynomial.trunc f).toLaurent=f := by
  ext e
  by_cases he:0≤e
  · lift e to ℕ using he
    rw [laurent_toLaurent_coeff,laurent_trunc_coeff]
  · rw [laurent_toLaurent_negative _ _ (by omega),h _ (by omega)]

lemma laurent_shift_coeff (f : LaurentPolynomial K) (a e : ℤ) :
    (f*LaurentPolynomial.T a).coeff e=f.coeff (e-a) := by
  simp only [LaurentPolynomial.T,AddMonoidAlgebra.coeff_mul_single_apply,mul_one]
  rfl

lemma LaurentInterval.shift {f : LaurentPolynomial K} {a b : ℤ}
    (h : LaurentInterval f a b) (c : ℤ) :
    LaurentInterval (f*LaurentPolynomial.T c) (a+c) (b+c) := by
  intro e he
  rw [laurent_shift_coeff] at he
  have := h (e-c) he
  omega

lemma LaurentInterval.shift_trunc {f : LaurentPolynomial K} {m : ℕ} {b : ℤ}
    (h : LaurentInterval f (-(m:ℤ)) b) :
    (LaurentPolynomial.trunc (f*LaurentPolynomial.T m)).toLaurent=
      f*LaurentPolynomial.T m := by
  apply laurent_toLaurent_trunc
  intro e he
  by_contra hh
  have := h.shift m e hh
  omega

 

theorem laurent_root_saturation (f : LaurentPolynomial K) (m : ℕ)
    (hb : LaurentInterval f (-(m:ℤ)) m) (htop : f.coeff (m:ℤ)=0)
    (s : Finset K) (hc : s.card=2*m) (hz : ∀ z∈s,z≠0)
    (he : ∀ z (h:z∈s),
      LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z h)) f=0) : f=0 := by
  let p := LaurentPolynomial.trunc (f*LaurentPolynomial.T m)
  have hp : p.degree<(2*m:ℕ) := by
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [laurent_trunc_coeff,laurent_shift_coeff]
    by_cases hh:k=2*m
    · subst k
      convert htop using 2
      push_cast
      ring
    · by_contra hn
      have := hb ((k:ℤ)-m) hn
      omega
  have hev (z : K) (hs:z∈s) : p.eval z=0 := by
    have h:=congrArg (LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs)))
      hb.shift_trunc
    rw [LaurentPolynomial.eval₂_toLaurent] at h
    change p.eval z = _ at h
    rw [(LaurentPolynomial.eval₂ (RingHom.id K) (Units.mk0 z (hz z hs))).map_mul,
      he z hs,zero_mul] at h
    exact h
  have hp0 : p=0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero s
    · simpa [hc] using hp
    · exact hev
  have hh:=hb.shift_trunc
  change p.toLaurent=_ at hh
  rw [hp0,map_zero] at hh
  have hunit:=LaurentPolynomial.isUnit_T (R:=K) (m:ℤ)
  exact (hunit.mul_left_eq_zero.mp hh.symm)

end
end CriticalStrip.Diagram

end OAI
