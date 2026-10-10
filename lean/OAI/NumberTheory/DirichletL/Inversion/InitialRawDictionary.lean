import OAI.NumberTheory.DirichletL.Inversion.InitialConjugateEnergy
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicBridge
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowSpecialization

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.InverseInitialRawDictionary
open HeckeFamily HeckeDyadic HeckeDetectorDyadicBridge HeckeRowClosure
open InverseInitialPoissonBridge InverseInitialConjugateEnergy
open ConcretePrimeRowBridge CompletedGauss UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def twistedProfile (W : ℝ → ℂ) (σ freq : ℝ) (x : ℝ) : ℂ :=
  W x*(x:ℂ)^(-shift σ freq)

theorem finite_source_cover (W : ℝ → ℂ) (D b : ℝ) (hD : 0<D)
    (hW : ∀x,W x≠0 → x≤b) (I : Ideal O) (hI : I≠0)
    (hi : W ((I.absNorm:ℝ)/D)≠0) : I∈idealsUpTo ⌈D*b⌉₊ := by
  apply mem_idealsUpTo.mpr
  refine ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI),?_⟩
  have hb := (div_le_iff₀ hD).mp (hW _ hi)
  have hn : (I.absNorm:ℝ)≤(⌈D*b⌉₊:ℝ) := by
    calc
      (I.absNorm:ℝ)≤D*b := by simpa only [mul_comm] using hb
      _≤(⌈D*b⌉₊:ℝ) := Nat.le_ceil _
  exact_mod_cast hn

theorem normalization_eq (Z r : ℝ) (hZ : 0<Z) :
    ((Z^r:ℝ):ℂ)^(-(1/2:ℂ))=((Z^(-r/2):ℝ):ℂ) := by
  have he : (-(1/2:ℂ))=((-(1/2:ℝ)):ℂ) := by norm_num
  calc
    _ = (((Z^r)^(-(1/2:ℝ)):ℝ):ℂ) := by
      simpa only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_one,
        Complex.ofReal_ofNat] using (Complex.ofReal_cpow
          (Real.rpow_nonneg hZ.le r) (-(1/2:ℝ))).symm
    _ = _ := ?_
  rw [←Real.rpow_mul hZ.le]
  congr 2
  ring

theorem inverse_eq_initial_source (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r σ freq : ℝ) (hZ : 0<Z) (S : Finset (Ideal O))
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial S 1 η (fun _=>1)
        (twistedProfile W σ freq) Z r 0 u := by
  rw [polynomial_eq_finite χ true W (Z^r) σ freq S hcover,normalization_eq Z r hZ]
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one]
  apply congrArg (fun x:ℂ=>((Z^(-r/2):ℝ):ℂ)*x)
  apply Finset.sum_congr rfl
  intro I hI
  simp only [coefficient,ite_true,hrow,heckeIdealCharacter_apply,
    twistedProfile]
  ring

theorem canonical_inverse_eq_initial_source (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial (idealsUpTo ⌈Z^r*b⌉₊) 1
        (idealCoeff η).toMonoidHom (fun _=>1)
        (twistedProfile W σ freq) Z r 0 (m^6*f^4*z) := by
  apply inverse_eq_initial_source (idealCoeff η).toMonoidHom χ (m^6*f^4*z)
    (HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow) W Z r σ freq hZ
  exact finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW

theorem inverse_times_mark_eq_initial (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*idealCoeff χ p)=
      ∑p∈P,A p*originalTotalPolynomial S p η
        (fun _=>1) (twistedProfile W σ freq) Z r z u := by
  rw [inverse_eq_initial_source η χ u hrow W Z r σ freq hZ S hcover]
  have hn : ((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ)=
      ((Z^(-(r+z)/2):ℝ):ℂ) := by
    rw [←Complex.ofReal_mul,←Real.rpow_add hZ]
    congr 2
    ring
  unfold originalTotalPolynomial
  simp only [add_zero,map_one,mul_one,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro I hI
  rw [hrow p]
  simp only [heckeIdealCharacter_apply]
  calc
    _ = (((Z^(-r/2):ℝ):ℂ)*((Z^(-z/2):ℝ):ℂ))*
      (A p*((moebius I:ℂ)*(η I*CanonicalRowCompletion.idealRowHom u I)*
      (η p*CanonicalRowCompletion.idealRowHom u p)*
      twistedProfile W σ freq ((I.absNorm:ℝ)/Z^r))) := by ring
    _ = _ := by rw [hn];ring

theorem originalTotal_supported_source (S : Finset (Ideal O)) (P : Ideal O)
    (η : Ideal O →* ℂ) (hη : ∀I,¬CanonicalQuadraticSieve.Supported I → η I=0)
    (a : Ideal O → ℂ) (W : ℝ → ℂ) (Z r z : ℝ) (u : O) :
    originalTotalPolynomial S P η a W Z r z u=
      originalTotalPolynomial (S.filter CanonicalQuadraticSieve.Supported) P η a W Z r z u := by
  unfold originalTotalPolynomial
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  split_ifs with hi
  · rfl
  · simp only [heckeIdealCharacter_apply,hη I hi,zero_mul,mul_zero]

def fixedBase (η : Character) (m f : O) : Ideal O →* ℂ :=
  heckeIdealCharacter (idealCoeff η).toMonoidHom (m^6*f^4)

theorem fixedBase_row (η χ : Character) (m f z : O)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n) (I : Ideal O) :
    idealCoeff χ I=fixedBase η m f I*CanonicalRowCompletion.idealRowHom z I := by
  rw [HeckeRowClosure.idealCoeff_eq_row η χ m f z hrow,
    CanonicalRowCompletion.idealRowHom_argument_mul]
  change idealCoeff η I*(CanonicalRowCompletion.idealRowHom (m^6*f^4) I*
    CanonicalRowCompletion.idealRowHom z I)=
    (idealCoeff η I*CanonicalRowCompletion.idealRowHom (m^6*f^4) I)*
    CanonicalRowCompletion.idealRowHom z I
  ring

theorem fixedBase_zero_unsupported (η : Character) (m f : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (I : Ideal O) (hI : ¬CanonicalQuadraticSieve.Supported I) : fixedBase η m f I=0 := by
  by_cases hi : I=0
  · subst I
    change idealCoeff η 0*_=0
    rw [map_zero,zero_mul]
  let n := ConcretePrimeRowBridge.idealGenerator I
  have hn : n≠0 := ConcretePrimeRowBridge.idealGenerator_ne_zero I hi
  have hs : Ideal.span {n}=I := ConcretePrimeRowBridge.span_idealGenerator I
  have he := CanonicalRowCompletion.rowTwist_zero_of_not_supported
    (elementHom η) m f 1 n hmLam hm2 (by rwa [hs])
  change elementCoeff η n*CanonicalRowCompletion.idealRowHom (m^6*f^4*1)
    (Ideal.span {n})=0 at he
  rw [mul_one,hs,←idealCoeff_span η hn,hs] at he
  exact he

theorem canonical_inverse_eq_supported_initial (η χ : Character) (m f z : O)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (hrow : ∀n:O,elementCoeff χ n=
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ → ℂ) (Z r σ freq b : ℝ) (hZ : 0<Z)
    (hW : ∀x,W x≠0 → x≤b) :
    polynomial χ true W (Z^r) σ freq=
      originalTotalPolynomial ((idealsUpTo ⌈Z^r*b⌉₊).filter CanonicalQuadraticSieve.Supported)
        1 (fixedBase η m f) (fun _=>1) (twistedProfile W σ freq) Z r 0 z := by
  rw [inverse_eq_initial_source (fixedBase η m f) χ z (fixedBase_row η χ m f z hrow)
    W Z r σ freq hZ (idealsUpTo ⌈Z^r*b⌉₊)
    (finite_source_cover W (Z^r) b (Real.rpow_pos_of_pos hZ r) hW)]
  exact originalTotal_supported_source _ _ _ (fixedBase_zero_unsupported η m f hmLam hm2)
    _ _ _ _ _ _

theorem inverse_times_conjugate_row_mark_norm (η : Ideal O →* ℂ) (χ : Character) (u : O)
    (hrow : ∀I,idealCoeff χ I=η I*CanonicalRowCompletion.idealRowHom u I)
    (W : ℝ → ℂ) (Z r z σ freq : ℝ) (hZ : 0<Z)
    (S P : Finset (Ideal O)) (A : Ideal O → ℂ)
    (hη : ∀p∈P,A p≠0 → η p≠0)
    (hcover : ∀I:Ideal O,I≠0 → W ((I.absNorm:ℝ)/Z^r)≠0 → I∈S) :
    ‖polynomial χ true W (Z^r) σ freq*(Z^(-z/2):ℝ)*
      (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p))‖=
    ‖∑p∈P,(star (A p)/η p)*originalTotalPolynomial S p η
      (fun _=>1) (twistedProfile W σ freq) Z r z u‖ := by
  have hm : (∑p∈P,(star (A p)/η p)*idealCoeff χ p)=
      star (∑p∈P,A p*star (CanonicalRowCompletion.idealRowHom u p)) := by
    simp only [star_sum,star_mul,star_star]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases ha : A p=0
    · simp [ha]
    · rw [hrow p]
      field_simp [hη p hp ha]
  rw [←inverse_times_mark_eq_initial η χ u hrow W Z r z σ freq hZ S P
    (fun p=>star (A p)/η p) hcover,hm]
  simp only [norm_mul,norm_star]

end SevenEighths.InverseInitialRawDictionary

end

end OAI
