import Mathlib
import OAI.Combinatorics.StripMass.RestrictedDiagrams

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section
open Finset

 
def lastTile {n : ℕ} (p q : Pairing (n+1)) : Tile := by
  classical
  exact if p.Occupied (Fin.last n) then
    if q.Occupied (Fin.last n) then .diagonal₁ else .cap
  else if q.Occupied (Fin.last n) then .vertical₀ else .vacant

theorem Realizes.last_eq {n : ℕ} {p q : Pairing (n+1)} {t : Configuration (n+1)}
    (h : Realizes p q t) : t (Fin.last n) = lastTile p q := by
  classical
  have hn := h.north (Fin.last n) rfl
  have hw := h.west (Fin.last n)
  have he := h.east (Fin.last n)
  unfold lastTile
  generalize t (Fin.last n) = a at hn hw he ⊢
  cases a <;> simp_all [Tile.Occupied, Tile.Adj, Tile.edges]

 

def lastCoefficient {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (q p : Pairing (n+1)) : K := by
  classical
  exact ∑ t : Configuration n,
    if Realizes p q (Fin.snoc t (lastTile p q)) then ∏ i, w i (t i) else 0

theorem lastCoefficient_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) {n : ℕ} (w : Fin n → Tile → K) (q p : Pairing (n+1)) :
    lastCoefficient (fun i a => f (w i a)) q p = f (lastCoefficient w q p) := by
  classical
  simp only [lastCoefficient, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp

 
theorem rawColumn_last_factor {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (r : Tile → K) (q p : Pairing (n+1)) :
    rawColumn (Fin.snoc w r) q p =
      lastCoefficient w q p * r (lastTile p q) := by
  classical
  unfold rawColumn
  rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (n+1) => Tile))
    (fun tt : Tile × Configuration n =>
      if Realizes p q (Fin.snoc tt.2 tt.1)
      then ∏ i : Fin (n+1), ((Fin.snoc w r : Fin (n+1) → Tile → K) i) ((Fin.snoc tt.2 tt.1 : Configuration (n+1)) i) else 0)
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (lastTile p q)]
  · simp only [lastCoefficient, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> simp [Fin.prod_univ_castSucc]
  · intro a ha hne
    apply Finset.sum_eq_zero
    intro t _
    have hnot : ¬ Realizes p q (Fin.snoc t a) := by
      intro h
      have hh := h.last_eq
      simp only [Fin.snoc_last] at hh
      exact hne hh
    simp [hnot]
  · simp

 
theorem lastCoefficient_padTop {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (q p : Pairing n) :
    lastCoefficient w q.padTop p.padTop = rawColumn w q p := by
  classical
  simp only [lastCoefficient, lastTile, Pairing.padTop_not_occupied_last,
    ite_false, realizes_snoc_top_iff, true_and, rawColumn]

 

def lastFactor {K : Type*} [CommRing K] {n : ℕ}
    (d c C : K) (p q : Pairing (n+1)) : Polynomial K := by
  classical
  exact if q.Occupied (Fin.last n) then
    if p.Occupied (Fin.last n) then Polynomial.X - Polynomial.C c
    else Polynomial.C (2*d)
  else if p.Occupied (Fin.last n) then Polynomial.C d * (Polynomial.X - Polynomial.C c)
    else Polynomial.X + Polynomial.C C

 

def lastTransform {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Tile → K) (d c C : K)
    (P : Pairing (n+1) → Polynomial K) (q : Pairing (n+1)) : Polynomial K :=
  ∑ p, Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p

 
def lastValue {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (b s : L) (P : Pairing (n+1) → Polynomial K)
    (p : Pairing (n+1)) : L := by
  classical
  exact if p.Occupied (Fin.last n) then s * (P p).eval₂ f b else (P p).eval₂ f b

 

theorem rawColumn_lastValue {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Tile → K) (d c C : K)
    (b s t : L) (r : Tile → L) (P : Pairing (n+1) → Polynomial K)
    (hv : r .vacant = b + f C) (hc : r .cap = 2 * f d * t)
    (hu : r .vertical₀ = 2 * f d * s) (hb : r .diagonal₁ = b - f c)
    (hst : 2 * s * t = b - f c) :
    (rawColumn (Fin.snoc (fun i a => f (w i a)) r)).mulVec (lastValue f b s P) =
      lastValue f b s (lastTransform w d c C P) := by
  classical
  funext q
  simp only [Matrix.mulVec, dotProduct, rawColumn_last_factor, lastCoefficient_map]
  have he (p : Pairing (n+1)) :
      f (lastCoefficient w q p) * r (lastTile p q) * lastValue f b s P p =
        if q.Occupied (Fin.last n) then
          s * (Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p).eval₂ f b
        else (Polynomial.C (lastCoefficient w q p) * lastFactor d c C p q * P p).eval₂ f b := by
    by_cases hp : p.Occupied (Fin.last n) <;> by_cases hq : q.Occupied (Fin.last n)
    all_goals simp [lastTile, lastValue, lastFactor, hp, hq, hv, hc, hu, hb, map_ofNat]
    all_goals try ring_nf
    calc
      _ = f (lastCoefficient w q p) * f d * (2*s*t) * (P p).eval₂ f b := by ring
      _ = _ := by rw [hst]; ring
  simp_rw [he]
  by_cases hq : q.Occupied (Fin.last n)
  · simp [lastValue, hq, lastTransform, Polynomial.eval₂_finsetSum, Finset.mul_sum]
  · simp [lastValue, hq, lastTransform, Polynomial.eval₂_finsetSum]

end

 

 

noncomputable section

 
def c : ℝ := Real.cos (3*lambda)

theorem phase_cosine (k : ℤ) : (phase^k+(phase^k)⁻¹)/2 =
    (Real.cos ((k:ℝ)*lambda) : ℂ) := by
  rw [phase_pow, Complex.ofReal_cos]
  push_cast
  rw [Complex.cos, ← Complex.exp_neg]
  simp only [neg_mul]

theorem phase_eight : phase^(8:ℕ) = -1 := by
  have h := phase_pow 8
  norm_num only [zpow_ofNat, Int.cast_ofNat] at h
  rw [h]
  convert Complex.exp_pi_mul_I using 1
  congr 1
  simp [lambda]
  ring

theorem constF_phase_eight (n : ℕ) : constF n phase ^ 8 = -1 := by
  rw [constF, ← map_pow, phase_eight, map_neg, map_one]

@[simp] theorem torusCos_inv {n : ℕ} (z : SpectralField n) :
    torusCos z⁻¹ = torusCos z := by simp [torusCos, add_comm]

@[simp] theorem torusCos_neg {n : ℕ} (z : SpectralField n) :
    torusCos (-z) = -torusCos z := by simp [torusCos]; ring

theorem torusCos_phase_pow (n : ℕ) (k : ℕ) :
    torusCos (constF n phase ^ k) = constF n (Real.cos ((k:ℝ)*lambda)) := by
  have h := congrArg (constF n) (phase_cosine (k:ℤ))
  simpa [torusCos, constF, map_ofNat] using h

theorem torusSin_product {n : ℕ} (z w : SpectralField n) (hz : z ≠ 0) (hw : w ≠ 0) :
    2 * torusSin z * torusSin w = torusCos (z/w) - torusCos (z*w) := by
  have hi : (constF n Complex.I)^2 = -1 := by
    simp only [constF, ← map_pow, Complex.I_sq, map_neg, map_one]
  have hI : constF n Complex.I ≠ 0 := by
    exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero
  unfold torusSin torusCos
  field_simp
  ring_nf
  rw [hi]
  ring

 
theorem spectral_sine_pair {n : ℕ} (i : Fin n) :
    2 * torusSin (variableF i) * torusSin (constF n phase ^ 3 / variableF i) =
      spectralA i - constF n c := by
  rw [torusSin_product _ _ (variableF_ne_zero i)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))]
  have h₁ : variableF i / (constF n phase ^ 3 / variableF i) =
      variableF i ^ 2 / constF n phase ^ 3 := by field_simp
  have h₂ : variableF i * (constF n phase ^ 3 / variableF i) = constF n phase ^ 3 := by
    field_simp [variableF_ne_zero i]
  rw [h₁, h₂, torusCos_phase_pow]
  rfl

 
theorem twice_rowDenominator {n : ℕ} (i : Fin n) :
    2 * evalLaurent (rowDenominator i) = spectralA i + constF n C := by
  rw [evalLaurent, rowDenominator_map, torusL]
  have hq := constF_phase_ne_zero n
  have hx := variableF_ne_zero i
  have h₅ : constF n phase ^ 2 * (constF n phase ^ 3 / variableF i) =
      constF n phase ^ 5 / variableF i := by ring
  have h₆ : constF n phase ^ 3 * (constF n phase ^ 3 / variableF i) =
      constF n phase ^ 6 / variableF i := by ring
  rw [h₅, h₆, ← mul_assoc, torusSin_product _ _
    (div_ne_zero (pow_ne_zero _ hq) hx) (div_ne_zero (pow_ne_zero _ hq) hx)]
  have hdiv : (constF n phase ^ 5 / variableF i) / (constF n phase ^ 6 / variableF i) =
      (constF n phase)⁻¹ := by field_simp
  have hmul : (constF n phase ^ 5 / variableF i) * (constF n phase ^ 6 / variableF i) =
      -(variableF i ^ 2 / constF n phase ^ 3)⁻¹ := by
    have h := constF_phase_eight n
    field_simp
    exact h
  rw [hdiv, hmul, torusCos_inv, torusCos_neg, torusCos_inv,
    ← pow_one (constF n phase), torusCos_phase_pow]
  simp only [Nat.cast_one, one_mul, sub_neg_eq_add]
  rw [add_comm]
  simp [spectralA, C]

 
def clearedSpectralRow {n : ℕ} (i : Fin n) (t : Tile) : SpectralField n :=
  (spectralA i + constF n C) * (spectralWeights n i).tile t

theorem clearedSpectralRow_eq {n : ℕ} (i : Fin n) (t : Tile) :
    clearedSpectralRow i t = 2 * evalLaurent (rowNumerator i t) := by
  rw [clearedSpectralRow, ← twice_rowDenominator]
  change (2 * algebraMap (SpectralRing n) (SpectralField n) (rowDenominator i)) * _ = _
  rw [mul_assoc, ← rowNumerator_map]
  rfl

@[simp] theorem clearedSpectralRow_vacant {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .vacant = spectralA i + constF n C := by
  simp [clearedSpectralRow, Weights.tile]

@[simp] theorem clearedSpectralRow_cap {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .cap = 2 * constF n d *
      torusSin (constF n phase ^ 3 / variableF i) := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul, map_constantL, zpow_ofNat,
    map_sine_neg_variable_nat, mul_assoc]

@[simp] theorem clearedSpectralRow_vertical₀ {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .vertical₀ = 2 * constF n d * torusSin (variableF i) := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul, map_constantL]
  rw [map_sine_variable i (0:ℤ)]
  simp only [zpow_zero, one_mul, mul_assoc]

@[simp] theorem clearedSpectralRow_diagonal₁ {n : ℕ} (i : Fin n) :
    clearedSpectralRow i .diagonal₁ = spectralA i - constF n c := by
  rw [clearedSpectralRow_eq]
  simp only [evalLaurent, rowNumerator, map_mul]
  rw [map_sine_variable i (0:ℤ), map_sine_neg_variable i (3:ℤ)]
  simp only [zpow_ofNat, pow_zero, one_mul]
  rw [mul_comm (torusSin _), ← mul_assoc, spectral_sine_pair]


 

 


 
def appendZero (n : ℕ) : (Fin n → ℤ) →+ (Fin (n+1) → ℤ) where
  toFun e := Fin.snoc e 0
  map_zero' := by
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp
  map_add' x y := by
    ext i
    refine Fin.lastCases ?_ (fun k => ?_) i <;> simp

def liftLaurentHom (n : ℕ) : Laurent n →+* Laurent (n+1) :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (appendZero n)

@[simp] theorem liftLaurentHom_apply {n : ℕ} (p : Laurent n) :
    liftLaurentHom n p = liftLaurent p := rfl

theorem appendZero_injective (n : ℕ) : Function.Injective (appendZero n) := by
  intro e f h
  funext i
  simpa [appendZero] using congrFun h i.castSucc

theorem liftLaurent_injective (n : ℕ) : Function.Injective (@liftLaurent n) :=
  AddMonoidAlgebra.mapDomain_injective (appendZero_injective n)

 

def liftSpectral (n : ℕ) : SpectralField n →+* SpectralField (n+1) :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (liftLaurentHom n))
    ((IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))).comp
      (liftLaurent_injective n))

@[simp] theorem liftSpectral_evalLaurent {n : ℕ} (p : Laurent n) :
    liftSpectral n (evalLaurent p) = evalLaurent (liftLaurent p) := by
  exact IsFractionRing.lift_algebraMap _ _

@[simp] theorem liftLaurent_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    liftLaurent (monomialL e z) = monomialL (Fin.snoc e 0) z := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem liftLaurent_const {n : ℕ} (z : ℂ) :
    liftLaurent (constantL n z) = constantL (n+1) z := by
  change liftLaurent (monomialL 0 z) = monomialL 0 z
  rw [liftLaurent_monomial]
  congr 1
  exact (appendZero n).map_zero

@[simp] theorem liftSpectral_const (n : ℕ) (z : ℂ) :
    liftSpectral n (constF n z) = constF (n+1) z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc, liftSpectral_evalLaurent, liftLaurent_const]
  exact map_constantL (n+1) z

@[simp] theorem appendZero_variable {n : ℕ} (i : Fin n) :
    Fin.snoc (variableExponent i) 0 = variableExponent i.castSucc := by
  ext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [variableExponent]
  · simp only [Fin.snoc_castSucc, variableExponent, Pi.single_apply,
      Fin.castSucc_inj]

@[simp] theorem liftSpectral_variable {n : ℕ} (i : Fin n) :
    liftSpectral n (variableF i) = variableF i.castSucc := by
  change liftSpectral n (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [liftSpectral_evalLaurent, liftLaurent_monomial, appendZero_variable]
  rfl

@[simp] theorem liftSpectral_torusSin {n : ℕ} (z : SpectralField n) :
    liftSpectral n (torusSin z) = torusSin (liftSpectral n z) := by
  simp [torusSin, map_div₀, map_inv₀, map_ofNat]

@[simp] theorem liftSpectral_torusCos {n : ℕ} (z : SpectralField n) :
    liftSpectral n (torusCos z) = torusCos (liftSpectral n z) := by
  simp [torusCos, map_div₀, map_inv₀, map_ofNat]

@[simp] theorem liftSpectral_spectralA {n : ℕ} (i : Fin n) :
    liftSpectral n (spectralA i) = spectralA i.castSucc := by
  simp [spectralA, map_div₀]

@[simp] theorem evalLaurent_lastSine (n : ℕ) :
    evalLaurent (lastSine n) = torusSin (variableF (Fin.last n)) := by
  have he : lastExponent n 1 = variableExponent (Fin.last n) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [lastExponent, variableExponent]
    · simp [lastExponent, variableExponent]
  have he' : lastExponent n (-1) = -variableExponent (Fin.last n) := by
    ext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [lastExponent, variableExponent]
    · simp [lastExponent, variableExponent]
  unfold lastSine
  change evalLaurent (monomialL (lastExponent n 1) _ - monomialL (lastExponent n (-1)) _) = _
  rw [he, he']
  simp only [evalLaurent, map_sub, map_monomialL_variable, map_monomialL_neg_variable]
  simp only [constF, map_div₀, map_mul, map_one, map_ofNat]
  simp only [torusSin, constF, div_eq_mul_inv]
  ring


 

 

open scoped Classical

namespace Weights
variable {K L : Type*} [CommRing K] [CommRing L]
def map (f : K →+* L) (w : Weights K) : Weights L :=
  ⟨f w.A,f w.B,f w.U,f w.E,f w.F⟩
@[simp] lemma map_tile (f : K →+* L) (w : Weights K) (t : Tile) :
    (w.map f).tile t=f (w.tile t) := by cases t <;> simp [map,tile]
end Weights

lemma column_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) :
    (column w).map f=column (fun i => (w i).map f) := by
  ext p q
  simp only [Matrix.map_apply,column,map_sum,Weights.map_tile]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> simp only [map_prod,map_zero]

lemma restrictedColumn_map {K L : Type*} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) :
    (restrictedColumn w).map f=restrictedColumn (fun i => (w i).map f) := by
  ext p q
  exact congrFun (congrFun (column_map f w) p.val) q.val

lemma VacuumRegular.map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) (h : VacuumRegular w) :
    VacuumRegular (fun i => (w i).map f) := by
  unfold VacuumRegular at h ⊢
  have hm : (1-restrictedColumn w).map f=1-restrictedColumn (fun i => (w i).map f) := by
    rw [←restrictedColumn_map]
    ext i j
    simp only [Matrix.map_apply,Matrix.sub_apply,Matrix.one_apply,map_sub]
    split_ifs <;> simp only [map_one,map_zero]
  have hh : f (1-restrictedColumn w).det≠0 := (map_ne_zero f).mpr h
  rw [f.map_det] at hh
  change ((1-restrictedColumn w).map f).det≠0 at hh
  rwa [hm] at hh

lemma normalizedVacuum_map {K L : Type*} [Field K] [Field L] {n : ℕ}
    (f : K →+* L) (w : Fin n → Weights K) (h : VacuumRegular w) :
    (fun p => f (normalizedVacuum w p))=normalizedVacuum (fun i => (w i).map f) := by
  apply normalizedVacuum_unique _ (h.map f w)
  have hs:=normalizedVacuum_stationary w h
  constructor
  · change f (normalizedVacuum w (empty n))=1
    rw [hs.1,map_one]
  · funext p
    have hh:=congrArg f (congrFun hs.2 p)
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul] at hh ⊢
    simpa only [←column_map,Matrix.map_apply] using hh

end

 

 

noncomputable section
open scoped Classical

def permExponent {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Fin n → ℤ) →+ (Fin n → ℤ) where
  toFun e := e ∘ σ.symm
  map_zero' := rfl
  map_add' _ _ := rfl

lemma permExponent_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permExponent σ) := by
  intro e f he
  funext i
  simpa [permExponent] using congrFun he (σ i)

def permLaurent {n : ℕ} (σ : Equiv.Perm (Fin n)) : Laurent n →+* Laurent n :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (permExponent σ)

lemma permLaurent_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permLaurent σ) :=
  AddMonoidAlgebra.mapDomain_injective (permExponent_injective σ)

def permSpectral {n : ℕ} (σ : Equiv.Perm (Fin n)) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (permLaurent σ))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (permLaurent_injective σ))

@[simp] lemma permSpectral_evalLaurent {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    permSpectral σ (evalLaurent f)=evalLaurent (permLaurent σ f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma permLaurent_monomial {n : ℕ} (σ : Equiv.Perm (Fin n))
    (e : Fin n → ℤ) (z : ℂ) : permLaurent σ (monomialL e z)=
      monomialL (e ∘ σ.symm) z := AddMonoidAlgebra.mapDomain_single

@[simp] lemma permSpectral_const {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : ℂ) :
    permSpectral σ (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,permSpectral_evalLaurent]
  change evalLaurent (permLaurent σ (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [permLaurent_monomial]
  rfl

@[simp] lemma permSpectral_variable {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (variableF i)=variableF (σ i) := by
  change permSpectral σ (evalLaurent (monomialL (variableExponent i) 1))=_
  rw [permSpectral_evalLaurent,permLaurent_monomial]
  congr 2
  funext j
  by_cases hij : j=σ i
  · subst j; simp [variableExponent]
  · have hne : σ.symm j≠i := fun he => hij (by simpa using congrArg σ he)
    simp [variableExponent,Function.comp_apply,hij,hne]

@[simp] lemma permSpectral_torusSin {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusSin z)=torusSin (permSpectral σ z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma permSpectral_torusCos {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusCos z)=torusCos (permSpectral σ z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma permSpectral_torusL {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    permSpectral σ (torusL z)=torusL (permSpectral σ z) := by simp [torusL]

@[simp] lemma permSpectral_torusWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (z : SpectralField n) :
    (torusWeights z).map (permSpectral σ)=torusWeights (permSpectral σ z) := by
  simp [Weights.map,torusWeights,map_div₀]

@[simp] lemma permSpectral_spectralWeights {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    (spectralWeights n i).map (permSpectral σ)=spectralWeights n (σ i) := by
  simp [spectralWeights,map_div₀]

@[simp] lemma permSpectral_spectralA {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    permSpectral σ (spectralA i)=spectralA (σ i) := by simp [spectralA,map_div₀]

lemma permSpectral_vacuum {n : ℕ} (σ : Equiv.Perm (Fin n)) (p : Pairing n) :
    permSpectral σ (normalizedVacuum (spectralWeights n) p)=
      normalizedVacuum (fun i => spectralWeights n (σ i)) p := by
  have h:=congrFun (normalizedVacuum_map (permSpectral σ) (spectralWeights n) (spectral_regular n)) p
  simpa using h

end
end CriticalStrip.Diagram

end OAI
