import Mathlib
import OAI.Combinatorics.StripMass.TopPadding

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
def rawRestricted {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Tile → R) :
    Matrix (NonemptyPairing n) (NonemptyPairing n) R :=
  (rawColumn w).submatrix Subtype.val Subtype.val

theorem column_eq_raw {R : Type*} [CommRing R] {n : ℕ} (w : Fin n → Weights R) :
    column w = rawColumn (fun i => (w i).tile) := rfl

theorem rawColumn_scale {R : Type*} [CommRing R] {n : ℕ}
    (w : Fin n → Tile → R) (a : Fin n → R) :
    rawColumn (fun i t => a i * w i t) = (∏ i, a i) • rawColumn w := by
  classical
  ext q p
  simp only [rawColumn, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp [Finset.prod_mul_distrib]

theorem rawColumn_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (w : Fin n → Tile → R) :
    (rawColumn w).map f = rawColumn (fun i t => f (w i t)) := by
  classical
  ext q p
  simp only [Matrix.map_apply, rawColumn, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs <;> simp

theorem rawRestricted_scale {R : Type*} [CommRing R] {n : ℕ}
    (w : Fin n → Tile → R) (a : Fin n → R) :
    rawRestricted (fun i t => a i * w i t) = (∏ i, a i) • rawRestricted w := by
  unfold rawRestricted
  rw [rawColumn_scale]
  rfl

theorem rawRestricted_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (w : Fin n → Tile → R) :
    (rawRestricted w).map f = rawRestricted (fun i t => f (w i t)) := by
  unfold rawRestricted
  rw [← rawColumn_map]
  rfl

theorem cleared_map {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (g : R →+* S) (num : Fin n → Tile → R) (a : Fin n → R)
    (w : Fin n → Weights S)
    (h : ∀ i t, g (num i t) = g (a i) * (w i).tile t) :
    (((∏ i, a i) • 1 - rawRestricted num).map g) =
      (∏ i, g (a i)) • (1 - restrictedColumn w) := by
    have hraw : (rawRestricted num).map g =
        (∏ i, g (a i)) • restrictedColumn w := by
      rw [rawRestricted_map]
      simp_rw [h]
      rw [rawRestricted_scale]
      rfl
    ext p q
    have hh := congrFun (congrFun hraw p) q
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hh
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, map_sub, map_mul, map_prod, Matrix.one_apply]
    rw [hh]
    split_ifs <;> simp
    ring

 

theorem regular_of_cleared_specialization {R K F : Type*}
    [CommRing R] [Field K] [Field F] {n : ℕ}
    (f : R →+* K) (hf : Function.Injective f) (e : R →+* F)
    (a : Fin n → R) (num : Fin n → Tile → R)
    (wa : Fin n → Weights K) (we : Fin n → Weights F)
    (ha : ∀ i, e (a i) ≠ 0)
    (hnuma : ∀ i t, f (num i t) = f (a i) * (wa i).tile t)
    (hnume : ∀ i t, e (num i t) = e (a i) * (we i).tile t)
    (he : VacuumRegular we) : VacuumRegular wa := by
  classical
  let A : Matrix (NonemptyPairing n) (NonemptyPairing n) R :=
    (∏ i, a i) • 1 - rawRestricted num
  have hAe : e A.det ≠ 0 := by
    rw [e.map_det]
    change (A.map e).det ≠ 0
    rw [show A.map e = _ from cleared_map e num a we hnume, Matrix.det_smul]
    apply mul_ne_zero
    · exact pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr (fun i _ => ha i))
    · exact he
  have hA : A.det ≠ 0 := by
    intro h
    exact hAe (by rw [h, map_zero])
  have hAf : f A.det ≠ 0 := by
    intro h
    exact hA (hf (by simpa using h))
  rw [f.map_det] at hAf
  change (A.map f).det ≠ 0 at hAf
  rw [show A.map f = _ from cleared_map f num a wa hnuma, Matrix.det_smul] at hAf
  exact (mul_ne_zero_iff.mp hAf).2

 

abbrev Laurent (n : ℕ) := AddMonoidAlgebra ℂ (Fin n → ℤ)
abbrev SpectralRing (n : ℕ) := Laurent n
abbrev SpectralField (n : ℕ) := FractionRing (SpectralRing n)

def constF (n : ℕ) (z : ℂ) : SpectralField n := algebraMap ℂ (SpectralField n) z

def variableExponent {n : ℕ} (i : Fin n) : Fin n → ℤ :=
  Pi.single i 1

def variableF {n : ℕ} (i : Fin n) : SpectralField n :=
  algebraMap (SpectralRing n) (SpectralField n)
    (AddMonoidAlgebra.single (variableExponent i) 1)

def phase : ℂ := Complex.exp (lambda * Complex.I)
def rho : ℝ := 1 / Real.sqrt (2 + Real.sqrt 2)
def d : ℝ := Real.cos (2*lambda)
def C : ℝ := Real.cos lambda

def torusSin {n : ℕ} (z : SpectralField n) : SpectralField n :=
  (z-z⁻¹) / (2*constF n Complex.I)

def torusCos {n : ℕ} (z : SpectralField n) : SpectralField n := (z+z⁻¹)/2

def torusL {n : ℕ} (z : SpectralField n) : SpectralField n :=
  torusSin (constF n phase ^ 2 * z) * torusSin (constF n phase ^ 3 * z)

 
def torusWeights {n : ℕ} (z : SpectralField n) : Weights (SpectralField n) :=
  let q := constF n phase
  let dd := constF n d
  let ell := torusL z
  ⟨dd * torusSin (q^3/z) / ell,
   torusSin z * torusSin (q^3/z) / ell,
   dd * torusSin z / ell,
   torusSin (q^3/z) * torusSin (q^2/z) / ell,
   torusSin (z/q) * torusSin z / ell⟩

 
def spectralWeights (n : ℕ) (i : Fin n) : Weights (SpectralField n) :=
  torusWeights (constF n phase ^ 3 / variableF i)

def spectralA {n : ℕ} (i : Fin n) : SpectralField n :=
  torusCos (variableF i ^ 2 / constF n phase ^ 3)

def discriminant {𝕜 : Type*} [CommRing 𝕜] (dd a b : 𝕜) : 𝕜 :=
  a^2+b^2+2*dd*a*b-dd^2

def pairFirst (n : ℕ) (i : Fin (n/2)) : Fin n := ⟨2*i.val, by have := i.isLt; omega⟩
def pairSecond (n : ℕ) (i : Fin (n/2)) : Fin n := ⟨2*i.val+1, by have := i.isLt; omega⟩

def pfaffian {𝕜 : Type*} [Field 𝕜] {n : ℕ} (M : Matrix (Fin n) (Fin n) 𝕜) : 𝕜 :=
  (2^(n/2) * (Nat.factorial (n/2) : 𝕜))⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) *
      ∏ i : Fin (n/2), M (σ (pairFirst n i)) (σ (pairSecond n i))

 
def augmentedKernel {𝕜 : Type*} [Field 𝕜] {n : ℕ} (dd rr : 𝕜) (a : Fin n → 𝕜) :
    Matrix (Fin (n+n%2)) (Fin (n+n%2)) 𝕜 := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then
      ((a ⟨i.val,hi⟩ - a ⟨j.val,hj⟩) * (a ⟨i.val,hi⟩ + a ⟨j.val,hj⟩ + rr)) /
        discriminant dd (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩)
    else 1
  else if j.val < n then -1 else 0

def scalarNormalization {𝕜 : Type*} [Field 𝕜] {n : ℕ} (dd rr : 𝕜) (a : Fin n → 𝕜) : 𝕜 :=
  (∏ i, ∏ j ∈ Finset.Ioi i, discriminant dd (a i) (a j) / (a i-a j)) *
    pfaffian (augmentedKernel dd rr a)

def spectralNormalization (n : ℕ) : SpectralField n :=
  scalarNormalization (constF n d) (constF n rho) spectralA

 
def evalLaurent {n : ℕ} (f : Laurent n) : SpectralField n :=
  algebraMap (SpectralRing n) (SpectralField n) f

def liftLaurent {n : ℕ} (f : Laurent n) : Laurent (n+1) :=
  AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain (fun e : Fin n → ℤ => Fin.snoc e 0) f.coeff)

def lastExponent (n : ℕ) (a : ℤ) : Fin (n+1) → ℤ := Fin.snoc (fun _ => 0) a

def lastCosine (n : ℕ) : Laurent (n+1) :=
  AddMonoidAlgebra.single (lastExponent n 2) (phase^(-3 : ℤ)/2) +
    AddMonoidAlgebra.single (lastExponent n (-2)) (phase^3/2)

def lastSine (n : ℕ) : Laurent (n+1) :=
  AddMonoidAlgebra.single (lastExponent n 1) (1/(2*Complex.I)) -
    AddMonoidAlgebra.single (lastExponent n (-1)) (1/(2*Complex.I))

 

def PolynomialVacuum : Prop :=
  ∃ W : (n : ℕ) → Pairing n → Laurent n,
    (W 0 (empty 0) = 1) ∧
    (∀ n p, evalLaurent (W n p) =
      spectralNormalization n * normalizedVacuum (spectralWeights n) p) ∧
    (∀ n p e, e ∈ (W n p).coeff.support → ∀ i, |e i| ≤ ((2*(n-1) : ℕ) : ℤ)) ∧
    (∀ n p, ∃ g : Fin n → Laurent n,
      W (n+1) p.padTop =
        liftLaurent (W n p) * lastCosine n ^ n +
          ∑ j : Fin n, liftLaurent (g j) * lastCosine n ^ j.val) ∧
    (∀ n (p : Pairing (n+1)), p.Occupied (Fin.last n) →
      ∃ g : Fin n → Laurent n,
        W (n+1) p = lastSine n *
          ∑ j : Fin n, liftLaurent (g j) * lastCosine n ^ j.val)


 
def monomialL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  AddMonoidAlgebra.single e z

def constantL (n : ℕ) : ℂ →+* Laurent n := AddMonoidAlgebra.singleZeroRingHom

def flatEval (n : ℕ) : Laurent n →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin n → ℤ) 1

@[simp] theorem flatEval_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    flatEval n (monomialL e z) = z := by
  simp [flatEval, monomialL, AddMonoidAlgebra.lift_single]

@[simp] theorem flatEval_constant (n : ℕ) (z : ℂ) :
    flatEval n (constantL n z) = z := flatEval_monomial 0 z

@[simp] theorem monomialL_mul {n : ℕ} (e f : Fin n → ℤ) (z w : ℂ) :
    monomialL e z * monomialL f w = monomialL (e+f) (z*w) := by
  exact AddMonoidAlgebra.single_mul_single _ _ _ _

@[simp] theorem monomialL_zero_one (n : ℕ) : monomialL (0 : Fin n → ℤ) 1 = 1 :=
  AddMonoidAlgebra.one_def.symm

theorem map_constantL (n : ℕ) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (constantL n z) = constF n z := by
  exact (IsScalarTower.algebraMap_apply ℂ (SpectralRing n) (SpectralField n) z).symm

theorem map_monomialL_inv {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    (algebraMap (SpectralRing n) (SpectralField n) (monomialL e z))⁻¹ =
      algebraMap (SpectralRing n) (SpectralField n) (monomialL (-e) z⁻¹) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul, monomialL_mul]
  simp [hz]

def sineL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  (monomialL e z - monomialL (-e) z⁻¹) * constantL n ((2*Complex.I)⁻¹)

theorem sineL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL e z) =
      torusSin (algebraMap (SpectralRing n) (SpectralField n) (monomialL e z)) := by
  rw [sineL, map_mul, map_sub, map_constantL]
  rw [torusSin, map_monomialL_inv e z hz]
  simp only [constF, map_inv₀, map_mul, map_ofNat, div_eq_mul_inv]

@[simp] theorem flatEval_sine {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    flatEval n (sineL e z) = (z-z⁻¹)/(2*Complex.I) := by
  simp [sineL, div_eq_mul_inv]

theorem phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _

theorem phase_pow (k : ℤ) : phase^k = Complex.exp ((k:ℂ)*lambda*Complex.I) := by
  rw [phase, ← Complex.exp_int_mul]
  congr 1
  ring

theorem phase_sine (k : ℤ) : (phase^k-(phase^k)⁻¹)/(2*Complex.I) =
    (Real.sin ((k:ℝ)*lambda) : ℂ) := by
  rw [phase_pow, Complex.ofReal_sin]
  push_cast
  rw [Complex.sin, ← Complex.exp_neg]
  field_simp
  simp [Complex.I_sq]

@[simp] theorem flatEval_sine_phase {n : ℕ} (e : Fin n → ℤ) (k : ℤ) :
    flatEval n (sineL e (phase^k)) = (Real.sin ((k:ℝ)*lambda) : ℂ) := by
  rw [flatEval_sine, phase_sine]

theorem variableF_ne_zero {n : ℕ} (i : Fin n) : variableF i ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  simp [AddMonoidAlgebra.single_eq_zero]

theorem map_monomialL_factor {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL e z) =
      constF n z * algebraMap (SpectralRing n) (SpectralField n) (monomialL e 1) := by
  rw [← map_constantL, ← map_mul]
  congr 1
  change monomialL e z = monomialL 0 z * monomialL e 1
  simp

theorem map_monomialL_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL (variableExponent i) z) =
      constF n z * variableF i := map_monomialL_factor _ z

theorem map_monomialL_neg_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    algebraMap (SpectralRing n) (SpectralField n) (monomialL (-variableExponent i) z) =
      constF n z / variableF i := by
  rw [map_monomialL_factor, div_eq_mul_inv]
  congr 1
  symm
  simpa only [variableF, monomialL, inv_one] using
    map_monomialL_inv (variableExponent i) 1 one_ne_zero

theorem constF_phase_ne_zero (n : ℕ) : constF n phase ≠ 0 := by
  exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr phase_ne_zero

theorem map_sine_variable {n : ℕ} (i : Fin n) (k : ℤ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k * variableF i) := by
  rw [sineL_map _ _ (zpow_ne_zero _ phase_ne_zero), map_monomialL_variable]
  congr 2
  exact map_zpow₀ (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_neg_variable {n : ℕ} (i : Fin n) (k : ℤ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (-variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k / variableF i) := by
  rw [sineL_map _ _ (zpow_ne_zero _ phase_ne_zero), map_monomialL_neg_variable]
  congr 2
  exact map_zpow₀ (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_variable_nat {n : ℕ} (i : Fin n) (k : ℕ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k * variableF i) := by
  rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_variable]
  congr 2
  exact map_pow (algebraMap ℂ (SpectralField n)) phase k

theorem map_sine_neg_variable_nat {n : ℕ} (i : Fin n) (k : ℕ) :
    algebraMap (SpectralRing n) (SpectralField n) (sineL (-variableExponent i) (phase^k)) =
      torusSin (constF n phase ^ k / variableF i) := by
  rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_neg_variable]
  congr 2
  exact map_pow (algebraMap ℂ (SpectralField n)) phase k


 
def rowDenominator {n : ℕ} (i : Fin n) : Laurent n :=
  sineL (-variableExponent i) (phase^(5:ℤ)) *
    sineL (-variableExponent i) (phase^(6:ℤ))

def rowNumerator {n : ℕ} (i : Fin n) : Tile → Laurent n
  | .vacant => rowDenominator i
  | .vertical₀ | .vertical₁ =>
      constantL n d * sineL (variableExponent i) (phase^(0:ℤ))
  | .diagonal₀ | .diagonal₁ =>
      sineL (-variableExponent i) (phase^(3:ℤ)) *
        sineL (variableExponent i) (phase^(0:ℤ))
  | .cap | .cup => constantL n d * sineL (-variableExponent i) (phase^(3:ℤ))
  | .verticalPair =>
      sineL (variableExponent i) (phase^(0:ℤ)) *
        sineL (variableExponent i) (phase^(-1:ℤ))
  | .capCup =>
      sineL (-variableExponent i) (phase^(2:ℤ)) *
        sineL (-variableExponent i) (phase^(3:ℤ))

theorem inlinePrivate0_sin_five_lambda : Real.sin (5*lambda) = Real.sin (3*lambda) := by
  rw [show 5*lambda = Real.pi-3*lambda by unfold lambda; ring, Real.sin_pi_sub]
theorem inlinePrivate0_sin_six_lambda : Real.sin (6*lambda) = Real.sin (2*lambda) := by
  rw [show 6*lambda = Real.pi-2*lambda by unfold lambda; ring, Real.sin_pi_sub]

theorem flatEval_rowDenominator {n : ℕ} (i : Fin n) :
    flatEval n (rowDenominator i) =
      (Real.sin (3*lambda) : ℂ) * (Real.sin (2*lambda) : ℂ) := by
  rw [rowDenominator, map_mul, flatEval_sine_phase, flatEval_sine_phase]
  norm_num only [Int.cast_ofNat]
  rw [inlinePrivate0_sin_five_lambda, inlinePrivate0_sin_six_lambda]

theorem flatEval_rowDenominator_ne_zero {n : ℕ} (i : Fin n) :
    flatEval n (rowDenominator i) ≠ 0 := by
  rw [flatEval_rowDenominator]
  exact mul_ne_zero (by exact_mod_cast ne_of_gt inlinePrivate0_sin_three_lambda_pos)
    (by exact_mod_cast ne_of_gt inlinePrivate0_sin_two_lambda_pos)

theorem rowDenominator_map {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) =
      torusL (constF n phase ^ 3 / variableF i) := by
  simp only [rowDenominator, map_mul, zpow_ofNat, map_sine_neg_variable_nat, torusL]
  congr 1 <;> congr 1 <;> ring

theorem rowDenominator_map_ne_zero {n : ℕ} (i : Fin n) :
    algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) ≠ 0 := by
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro h
  exact flatEval_rowDenominator_ne_zero i (by rw [h, map_zero])

theorem rowNumerator_flatEval {n : ℕ} (i : Fin n) (t : Tile) :
    flatEval n (rowNumerator i t) =
      flatEval n (rowDenominator i) * (deletionWeights : Weights ℂ).tile t := by
  cases t <;> simp only [rowNumerator, map_mul, flatEval_constant,
    flatEval_sine_phase, flatEval_rowDenominator, deletionWeights, Weights.tile,
    Int.cast_ofNat, Int.cast_zero, zero_mul, Real.sin_zero, Complex.ofReal_zero,
    mul_zero, mul_one]
  all_goals try rw [d, ← inlinePrivate0_sin_two_lambda]
  all_goals ring

theorem rowNumerator_map {n : ℕ} (i : Fin n) (t : Tile) :
    algebraMap (SpectralRing n) (SpectralField n) (rowNumerator i t) =
      algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i) *
        (spectralWeights n i).tile t := by
  let q : SpectralField n := constF n phase
  let x : SpectralField n := variableF i
  have hq : q ≠ 0 := constF_phase_ne_zero n
  have hx : x ≠ 0 := variableF_ne_zero i
  have h₃ : q^3 / (q^3/x) = x := by field_simp
  have h₂ : q^2 / (q^3/x) = q⁻¹*x := by field_simp
  have h₁ : q^3/x/q = q^2/x := by field_simp
  have hL : torusL (q^3/x) ≠ 0 := by
    simpa only [rowDenominator_map] using rowDenominator_map_ne_zero i
  dsimp only [q, x] at h₃ h₂ h₁ hL
  cases t <;>
    simp only [rowNumerator, map_mul, map_constantL,
      zpow_ofNat, map_sine_variable_nat, map_sine_neg_variable_nat, zpow_neg_one,
      rowDenominator_map, spectralWeights, torusWeights, Weights.tile]
  all_goals try simp only [h₃, h₂, h₁, mul_one]
  all_goals field_simp
  rw [sineL_map _ _ (one_div_ne_zero phase_ne_zero), map_monomialL_variable]
  simp only [constF, one_div, map_inv₀]
  rw [mul_comm ((algebraMap ℂ (SpectralField n)) phase)⁻¹, ← div_eq_mul_inv]

 

theorem spectral_regular (n : ℕ) : VacuumRegular (spectralWeights n) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective _ _) (flatEval n).toRingHom
    rowDenominator rowNumerator (spectralWeights n) (fun _ => deletionWeights)
  · exact flatEval_rowDenominator_ne_zero
  · exact rowNumerator_map
  · exact rowNumerator_flatEval
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro i j hi
      exact (hi (Or.inr rfl)).elim

theorem spectral_normalizedVacuum_stationary (n : ℕ) :
    IsNormalizedStationary (spectralWeights n) (normalizedVacuum (spectralWeights n)) :=
  normalizedVacuum_stationary _ (spectral_regular n)
end

end CriticalStrip.Diagram

end OAI
