import Mathlib
import OAI.Combinatorics.StripMass.RestrictedDiagrams

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

 

theorem pfaffian_reindex {K : Type*} [Field K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) :
    pfaffian (fun i j => M (τ i) (τ j)) =
      (Equiv.Perm.sign τ : ℤ) * pfaffian M := by
  classical
  unfold pfaffian
  have hsign : ((Equiv.Perm.sign τ : ℤ) : K) *
      ((Equiv.Perm.sign τ : ℤ) : K) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> simp [hs]
  have hs : (∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) *
      ∏ i : Fin (n/2), M (τ (σ (pairFirst n i))) (τ (σ (pairSecond n i)))) =
      ((Equiv.Perm.sign τ : ℤ) : K) *
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : K) *
        ∏ i : Fin (n/2), M (σ (pairFirst n i)) (σ (pairSecond n i)) := by
    rw [mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ ?_
    intro σ
    change _ = ((Equiv.Perm.sign τ : ℤ) : K) *
      (((Equiv.Perm.sign (τ*σ) : ℤ) : K) *
        ∏ i : Fin (n/2), M ((τ*σ) (pairFirst n i)) ((τ*σ) (pairSecond n i)))
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, map_mul, Units.val_mul, Int.cast_mul]
    rw [← mul_assoc, ← mul_assoc, hsign, one_mul]
  rw [hs]
  ring

 
abbrev UpperPair (n : ℕ) := {ij : Fin n × Fin n // ij.1 < ij.2}

instance (n : ℕ) : Fintype (UpperPair n) := by classical exact Subtype.fintype _

 
def upperPair {n : ℕ} (i j : Fin n) (h : i ≠ j) : UpperPair n :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt hij) h.symm⟩

theorem upperPair_symm {n : ℕ} (i j : Fin n) (h : i ≠ j) :
    upperPair i j h = upperPair j i h.symm := by
  by_cases hij : i < j
  · have hji : ¬ j < i := not_lt_of_ge hij.le
    simp [upperPair, hij, hji]
  · have hji : j < i := lt_of_le_of_ne (le_of_not_gt hij) h.symm
    simp [upperPair, hij, hji]

theorem upperPair_eq_iff {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d) :
    upperPair a b hab = upperPair c d hcd ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  unfold upperPair
  split_ifs <;> simp only [Subtype.mk.injEq, Prod.mk.injEq] <;> omega

theorem pairFirst_ne_pairSecond {n : ℕ} (i j : Fin (n/2)) :
    pairFirst n i ≠ pairSecond n j := by
  intro h
  have := congrArg Fin.val h
  simp only [pairFirst, pairSecond] at this
  omega

def permutationPair {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n/2)) : UpperPair n :=
  upperPair (σ (pairFirst n i)) (σ (pairSecond n i))
    (σ.injective.ne (pairFirst_ne_pairSecond i i))

theorem permutationPair_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (permutationPair σ) := by
  intro i j h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · have h₁ := σ.injective h.1
    have hv := congrArg Fin.val h₁
    apply Fin.ext
    simp only [pairFirst] at hv
    omega
  · exact False.elim (pairFirst_ne_pairSecond i j (σ.injective h.1))


 

 


theorem upperPair_value {R : Type*} {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (i j : Fin n) (h : i ≠ j) :
    D (upperPair i j h).val.1 (upperPair i j h).val.2 = D i j := by
  unfold upperPair
  split_ifs <;> simp [hD]

 
def selectedPairs {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (UpperPair n) :=
  Finset.univ.image (permutationPair σ)

 

def clearedPfaffianTerm {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n)) : R :=
  (∏ i : Fin (n/2), N (σ (pairFirst n i)) (σ (pairSecond n i))) *
    ∏ e ∈ (selectedPairs σ)ᶜ, D e.val.1 e.val.2

def clearedPfaffian {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (N D : Matrix (Fin n) (Fin n) R) : R :=
  t * ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * clearedPfaffianTerm N D σ

theorem prod_selectedPairs {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    (∏ e ∈ selectedPairs σ, D e.val.1 e.val.2) =
      ∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i)) := by
  rw [selectedPairs, Finset.prod_image]
  · apply Finset.prod_congr rfl
    intro i _
    exact upperPair_value D hD _ _ _
  · exact fun i _ j _ h => permutationPair_injective σ h

theorem clearedPfaffianTerm_mul_denominator {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    clearedPfaffianTerm N D σ *
        (∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i))) =
      (∏ i : Fin (n/2), N (σ (pairFirst n i)) (σ (pairSecond n i))) *
        ∏ e : UpperPair n, D e.val.1 e.val.2 := by
  rw [clearedPfaffianTerm, mul_assoc, ← prod_selectedPairs D hD σ,
    Finset.prod_compl_mul_prod]

theorem clear_pfaffian {K : Type*} [Field K] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) K) (hD : ∀ i j, D i j = D j i)
    (hne : ∀ i j, i ≠ j → D i j ≠ 0) :
    (∏ e : UpperPair n, D e.val.1 e.val.2) *
        pfaffian (fun i j => N i j / D i j) =
      clearedPfaffian (2^(n/2) * (Nat.factorial (n/2) : K))⁻¹ N D := by
  classical
  unfold pfaffian clearedPfaffian
  rw [mul_left_comm, mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_left_comm]
  congr 1
  rw [Finset.prod_div_distrib]
  have hd : (∏ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact hne _ _ (σ.injective.ne (pairFirst_ne_pairSecond i i))
  rw [← mul_div_assoc, div_eq_iff hd]
  rw [clearedPfaffianTerm_mul_denominator N D hD σ]
  ring

@[simp] theorem map_clearedPfaffianTerm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (N D : Matrix (Fin n) (Fin n) R) (σ : Equiv.Perm (Fin n)) :
    f (clearedPfaffianTerm N D σ) = clearedPfaffianTerm (N.map f) (D.map f) σ := by
  simp [clearedPfaffianTerm, Matrix.map_apply]

@[simp] theorem map_clearedPfaffian {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (t : R) (N D : Matrix (Fin n) (Fin n) R) :
    f (clearedPfaffian t N D) = clearedPfaffian (f t) (N.map f) (D.map f) := by
  simp [clearedPfaffian]


 

 


 

def augmentedNumerator {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) : Matrix (Fin (n+n%2)) (Fin (n+n%2)) R := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then
      (a ⟨i.val,hi⟩-a ⟨j.val,hj⟩)*(a ⟨i.val,hi⟩+a ⟨j.val,hj⟩+rr)
    else 1
  else if j.val < n then -1 else 0

def augmentedDenominator {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) : Matrix (Fin (n+n%2)) (Fin (n+n%2)) R := fun i j =>
  if hi : i.val < n then
    if hj : j.val < n then discriminant dd (a ⟨i.val,hi⟩) (a ⟨j.val,hj⟩)
    else 1
  else 1

theorem discriminant_symm {R : Type*} [CommRing R] (dd a b : R) :
    discriminant dd a b = discriminant dd b a := by unfold discriminant; ring

theorem augmentedDenominator_symm {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) (i j : Fin (n+n%2)) :
    augmentedDenominator dd a i j = augmentedDenominator dd a j i := by
  unfold augmentedDenominator
  split_ifs <;> try rfl
  exact discriminant_symm _ _ _

theorem augmentedKernel_eq {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (i j : Fin (n+n%2)) :
    augmentedKernel dd rr a i j =
      augmentedNumerator rr a i j / augmentedDenominator dd a i j := by
  unfold augmentedKernel augmentedNumerator augmentedDenominator
  split_ifs <;> simp

@[simp] theorem map_augmentedNumerator {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (rr : R) (a : Fin n → R) :
    (augmentedNumerator rr a).map f = augmentedNumerator (f rr) (fun i => f (a i)) := by
  ext i j
  simp only [Matrix.map_apply, augmentedNumerator]
  split_ifs <;> simp

@[simp] theorem map_augmentedDenominator {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}
    (f : R →+* S) (dd : R) (a : Fin n → R) :
    (augmentedDenominator dd a).map f = augmentedDenominator (f dd) (fun i => f (a i)) := by
  ext i j
  simp only [Matrix.map_apply, augmentedDenominator]
  split_ifs <;> simp [discriminant, map_ofNat]

abbrev CosineRing (n : ℕ) := MvPolynomial (Fin n) ℂ
abbrev CosineField (n : ℕ) := FractionRing (CosineRing n)

def cosineVar {n : ℕ} (i : Fin n) : CosineField n :=
  algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i)

def cosineConst (n : ℕ) (z : ℂ) : CosineField n :=
  algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C z)

 

def scalarNumerator (n : ℕ) (dd rr : ℂ) : CosineRing n :=
  clearedPfaffian (MvPolynomial.C ((2^((n+n%2)/2) *
    (Nat.factorial ((n+n%2)/2) : ℂ))⁻¹))
      (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X)
      (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X)

theorem discriminant_cosineVar_ne {n : ℕ} (dd : ℂ) (hdd : dd ≠ 0) (i j : Fin n) :
    discriminant (cosineConst n dd) (cosineVar i) (cosineVar j) ≠ 0 := by
  change discriminant (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C dd))
    (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i))
    (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X j)) ≠ 0
  have hmap : discriminant (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.C dd))
      (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X i))
      (algebraMap (CosineRing n) (CosineField n) (MvPolynomial.X j)) =
      algebraMap (CosineRing n) (CosineField n)
        (discriminant (MvPolynomial.C dd) (MvPolynomial.X i) (MvPolynomial.X j)) := by
    simp [discriminant, map_ofNat]
  rw [hmap]
  apply (map_ne_zero_iff _ (IsFractionRing.injective (CosineRing n) (CosineField n))).mpr
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin n => (0 : ℂ))) h
  simp [discriminant, hdd] at hh

theorem augmentedDenominator_cosineVar_ne {n : ℕ} (dd : ℂ) (hdd : dd ≠ 0)
    (i j : Fin (n+n%2)) :
    augmentedDenominator (cosineConst n dd) cosineVar i j ≠ 0 := by
  unfold augmentedDenominator
  split_ifs <;> try exact one_ne_zero
  exact discriminant_cosineVar_ne dd hdd _ _

theorem scalarNumerator_generic (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) :
    algebraMap (CosineRing n) (CosineField n) (scalarNumerator n dd rr) =
      (∏ e : UpperPair (n+n%2),
        augmentedDenominator (cosineConst n dd) cosineVar e.val.1 e.val.2) *
        pfaffian (augmentedKernel (cosineConst n dd) (cosineConst n rr) cosineVar) := by
  rw [scalarNumerator, map_clearedPfaffian, map_augmentedNumerator, map_augmentedDenominator]
  change clearedPfaffian _ (augmentedNumerator (cosineConst n rr) cosineVar)
    (augmentedDenominator (cosineConst n dd) cosineVar) = _
  have ht : algebraMap (CosineRing n) (CosineField n)
      (MvPolynomial.C ((2^((n+n%2)/2) * (Nat.factorial ((n+n%2)/2) : ℂ))⁻¹)) =
      (2^((n+n%2)/2) * (Nat.factorial ((n+n%2)/2) : CosineField n))⁻¹ := by
    let f : ℂ →+* CosineField n :=
      (algebraMap (CosineRing n) (CosineField n)).comp MvPolynomial.C
    change f _ = _
    simp only [map_inv₀, map_mul, map_pow, map_ofNat, map_natCast]
  rw [ht, ← clear_pfaffian _ _ (augmentedDenominator_symm _ _)
    (fun i j _ => augmentedDenominator_cosineVar_ne dd hdd i j)]
  congr 2
  ext i j
  exact (augmentedKernel_eq _ _ _ i j).symm


 

 


def upperPairMap {n : ℕ} (σ : Equiv.Perm (Fin n)) (e : UpperPair n) : UpperPair n :=
  upperPair (σ e.val.1) (σ e.val.2) (σ.injective.ne (ne_of_lt e.property))

theorem upperPairMap_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (upperPairMap σ) := by
  intro e f h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · apply Subtype.ext
    exact Prod.ext (σ.injective h.1) (σ.injective h.2)
  · have h₁ := σ.injective h.1
    have h₂ := σ.injective h.2
    have hef := e.property
    rw [h₁, h₂] at hef
    exact False.elim (lt_asymm hef f.property)

def upperPairPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (UpperPair n) :=
  Equiv.ofBijective (upperPairMap σ)
    ⟨upperPairMap_injective σ, Finite.surjective_of_injective (upperPairMap_injective σ)⟩

 
theorem prod_upperPair_reindex {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i) (σ : Equiv.Perm (Fin n)) :
    (∏ e : UpperPair n, D (σ e.val.1) (σ e.val.2)) =
      ∏ e : UpperPair n, D e.val.1 e.val.2 := by
  refine Fintype.prod_equiv (upperPairPerm σ) _ _ ?_
  intro e
  exact (upperPair_value D hD _ _ (σ.injective.ne (ne_of_lt e.property))).symm

theorem prod_upperPair {R : Type*} [CommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) :
    (∏ e : UpperPair n, D e.val.1 e.val.2) =
      ∏ i, ∏ j ∈ Finset.Ioi i, D i j := by
  rw [← Finset.prod_subtype (Finset.univ.filter (fun ij : Fin n × Fin n => ij.1 < ij.2))
    (by simp) (fun ij : Fin n × Fin n => D ij.1 ij.2), Finset.prod_filter]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro i _
  have h : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by ext j; simp
  rw [h, Finset.prod_filter]

 
def upperPairEmbed {n m : ℕ} (h : n ≤ m) (e : UpperPair n) : UpperPair m :=
  ⟨(e.val.1.castLE h,e.val.2.castLE h),e.property⟩

theorem upperPairEmbed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (upperPairEmbed h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun e : Fin m × Fin m => e.1.val) hv
  · apply Fin.ext
    exact congrArg (fun e : Fin m × Fin m => e.2.val) hv


 

 


theorem scalarNumerator_eval {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      (∏ e : UpperPair (n+n%2), augmentedDenominator (f dd) a e.val.1 e.val.2) *
        pfaffian (augmentedKernel (f dd) (f rr) a) := by
  rw [scalarNumerator, map_clearedPfaffian, map_augmentedNumerator, map_augmentedDenominator]
  simp only [MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X',
    map_inv₀, map_mul, map_pow, map_ofNat, map_natCast]
  have hn : ∀ i j, i ≠ j → augmentedDenominator (f dd) a i j ≠ 0 := by
    intro i j hij
    unfold augmentedDenominator
    split_ifs with hi hj <;> try exact one_ne_zero
    apply hD
    intro h
    exact hij (Fin.ext (congrArg (fun k : Fin n => k.val) h))
  rw [← clear_pfaffian _ _ (augmentedDenominator_symm _ _) hn]
  congr 2
  ext i j
  exact (augmentedKernel_eq _ _ _ i j).symm

theorem product_augmentedDenominator {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) :
    (∏ e : UpperPair (n+n%2), augmentedDenominator dd a e.val.1 e.val.2) =
      ∏ i, ∏ j ∈ Finset.Ioi i, discriminant dd (a i) (a j) := by
  let hn : n ≤ n+n%2 := Nat.le_add_right _ _
  rw [← prod_upperPair]
  symm
  apply Fintype.prod_of_injective (upperPairEmbed hn) (upperPairEmbed_injective hn)
  · intro e he
    unfold augmentedDenominator
    split_ifs with hi hj
    · exfalso
      apply he
      refine ⟨⟨(⟨e.val.1.val,hi⟩,⟨e.val.2.val,hj⟩),e.property⟩,?_⟩
      apply Subtype.ext
      exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
    · rfl
    · rfl
  · intro e
    simp [upperPairEmbed, augmentedDenominator, e.val.1.isLt, e.val.2.isLt]

 

theorem scalarNumerator_eval_vandermonde {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K) (ha : Function.Injective a)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0) :
    MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) =
      (∏ i, ∏ j ∈ Finset.Ioi i, (a i-a j)) * scalarNormalization (f dd) (f rr) a := by
  rw [scalarNumerator_eval f n dd rr a hD, product_augmentedDenominator]
  unfold scalarNormalization
  rw [← prod_upperPair, ← prod_upperPair, ← prod_upperPair,
    Finset.prod_div_distrib]
  have hv : (∏ e : UpperPair n, (a e.val.1-a e.val.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro e _
    exact sub_ne_zero.mpr (ha.ne (ne_of_lt e.property))
  field_simp


 

 


def augmentedPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+n%2)) :=
  σ.viaEmbedding (Fin.castAddEmb (n%2))

@[simp] theorem augmentedPerm_real {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    augmentedPerm σ (i.castAdd (n%2)) = (σ i).castAdd (n%2) :=
  Equiv.Perm.viaEmbedding_apply σ (Fin.castAddEmb (n%2)) i

theorem augmentedPerm_extra {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin (n+n%2)) (hi : ¬ i.val < n) : augmentedPerm σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨j,hj⟩
  apply hi
  rw [← hj]
  exact j.isLt

theorem augmentedPerm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin (n+n%2)) :
    augmentedPerm σ i = if hi : i.val < n then (σ ⟨i.val,hi⟩).castAdd (n%2) else i := by
  split_ifs with hi
  · exact augmentedPerm_real σ ⟨i.val,hi⟩
  · exact augmentedPerm_extra σ i hi

@[simp] theorem augmentedPerm_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.sign (augmentedPerm σ) = Equiv.Perm.sign σ := by
  classical
  unfold augmentedPerm Equiv.Perm.viaEmbedding
  exact @Equiv.Perm.sign_extendDomain _ _ _ _ _ _ σ _
    (fun a => Classical.propDecidable _) _

theorem augmentedNumerator_reindex {R : Type*} [CommRing R] {n : ℕ}
    (rr : R) (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    augmentedNumerator rr (a ∘ σ) =
      fun i j => augmentedNumerator rr a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
    simp [augmentedNumerator, augmentedPerm_apply, hi, hj, Function.comp_apply]

theorem augmentedDenominator_reindex {R : Type*} [CommRing R] {n : ℕ}
    (dd : R) (a : Fin n → R) (σ : Equiv.Perm (Fin n)) :
    augmentedDenominator dd (a ∘ σ) =
      fun i j => augmentedDenominator dd a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  by_cases hi : i.val < n <;> by_cases hj : j.val < n <;>
    simp [augmentedDenominator, augmentedPerm_apply, hi, hj, Function.comp_apply]

theorem augmentedKernel_reindex {K : Type*} [Field K] {n : ℕ}
    (dd rr : K) (a : Fin n → K) (σ : Equiv.Perm (Fin n)) :
    augmentedKernel dd rr (a ∘ σ) =
      fun i j => augmentedKernel dd rr a (augmentedPerm σ i) (augmentedPerm σ j) := by
  ext i j
  rw [augmentedKernel_eq, augmentedKernel_eq, augmentedNumerator_reindex,
    augmentedDenominator_reindex]

 

theorem scalarNumerator_eval_reindex {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (dd rr : ℂ) (a : Fin n → K)
    (hD : ∀ i j, i ≠ j → discriminant (f dd) (a i) (a j) ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.eval₂Hom f (a ∘ σ) (scalarNumerator n dd rr) =
      (Equiv.Perm.sign σ : ℤ) * MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  have hDσ : ∀ i j, i ≠ j → discriminant (f dd) ((a ∘ σ) i) ((a ∘ σ) j) ≠ 0 := by
    intro i j hij
    exact hD _ _ (σ.injective.ne hij)
  rw [scalarNumerator_eval f n dd rr _ hDσ, scalarNumerator_eval f n dd rr _ hD,
    augmentedDenominator_reindex, augmentedKernel_reindex,
    prod_upperPair_reindex _ (augmentedDenominator_symm _ _), pfaffian_reindex,
    augmentedPerm_sign]
  ring

def cosineCoeff (n : ℕ) : ℂ →+* CosineField n :=
  (algebraMap (CosineRing n) (CosineField n)).comp MvPolynomial.C

@[simp] theorem cosineCoeff_apply (n : ℕ) (z : ℂ) : cosineCoeff n z = cosineConst n z := rfl

theorem eval₂_cosineCoeff (n : ℕ) :
    MvPolynomial.eval₂Hom (cosineCoeff n) cosineVar =
      algebraMap (CosineRing n) (CosineField n) := by
  ext a <;> simp [cosineCoeff, cosineVar]

 

theorem scalarNumerator_rename {n : ℕ} (dd rr : ℂ) (hdd : dd ≠ 0)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.rename σ (scalarNumerator n dd rr) =
      (Equiv.Perm.sign σ : ℤ) * scalarNumerator n dd rr := by
  apply IsFractionRing.injective (CosineRing n) (CosineField n)
  rw [← eval₂_cosineCoeff, MvPolynomial.eval₂Hom_rename, map_mul, map_intCast]
  exact scalarNumerator_eval_reindex (cosineCoeff n) n dd rr cosineVar
    (fun i j _ => discriminant_cosineVar_ne dd hdd i j) σ

end
end CriticalStrip.Diagram

end OAI
