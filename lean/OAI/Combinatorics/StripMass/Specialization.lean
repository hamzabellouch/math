import Mathlib
import OAI.Combinatorics.StripMass.LaurentNumerator

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



 

namespace CriticalStrip.Diagram
noncomputable section

variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F]

 
def RationalAt (φ : R →+* K) (x : F) (y : K) : Prop :=
  ∃ a b : R, φ b ≠ 0 ∧ x * algebraMap R F b = algebraMap R F a ∧ y * φ b = φ a

namespace RationalAt
variable {φ : R →+* K} {x x' : F} {y y' : K}

omit [IsDomain R] [IsFractionRing R F] in
theorem algebraMap (a : R) : RationalAt φ (algebraMap R F a) (φ a) := by
  exact ⟨a, 1, by simp, by simp, by simp⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem zero : RationalAt φ (0 : F) (0 : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (0 : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem one : RationalAt φ (1 : F) (1 : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (1 : R))

omit [IsDomain R] in
theorem unique (h : RationalAt φ x y) (h' : RationalAt φ x y') : y = y' := by
  obtain ⟨a, b, hb, he, hv⟩ := h
  obtain ⟨a', b', hb', he', hv'⟩ := h'
  have hab : a * b' = a' * b := by
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, ← he, ← he']
    ring
  have hvv := congrArg φ hab
  simp only [map_mul, ← hv, ← hv'] at hvv
  apply mul_right_cancel₀ (mul_ne_zero hb hb')
  calc
    y * (φ b * φ b') = (y * φ b) * φ b' := by ring
    _ = (y' * φ b') * φ b := hvv
    _ = y' * (φ b * φ b') := by ring

omit [IsDomain R] [IsFractionRing R F] in
theorem add (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x+x') (y+y') := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  obtain ⟨a',b',hb',he',hv'⟩ := h'
  refine ⟨a*b'+a'*b, b*b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [_root_.map_mul, _root_.map_add, ← he, ← he']; ring
  · simp only [_root_.map_mul, _root_.map_add, ← hv, ← hv']; ring

omit [IsDomain R] [IsFractionRing R F] in
theorem mul (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x*x') (y*y') := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  obtain ⟨a',b',hb',he',hv'⟩ := h'
  refine ⟨a*a', b*b', by simpa using mul_ne_zero hb hb', ?_, ?_⟩
  · simp only [_root_.map_mul, ← he, ← he']; ring
  · simp only [_root_.map_mul, ← hv, ← hv']; ring

omit [IsDomain R] [IsFractionRing R F] in
theorem neg (h : RationalAt φ x y) : RationalAt φ (-x) (-y) := by
  obtain ⟨a,b,hb,he,hv⟩ := h
  exact ⟨-a,b,hb, by simp [← he], by simp [← hv]⟩

omit [IsDomain R] [IsFractionRing R F] in
theorem sub (h : RationalAt φ x y) (h' : RationalAt φ x' y') :
    RationalAt φ (x-x') (y-y') := by simpa only [sub_eq_add_neg] using h.add h'.neg

omit [IsDomain R] in
theorem ne_zero (h : RationalAt φ x y) (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  rw [hx] at h
  exact hy (h.unique zero)

omit [IsDomain R] in
theorem inv (h : RationalAt φ x y) (hy : y ≠ 0) : RationalAt φ x⁻¹ y⁻¹ := by
  have hx := h.ne_zero hy
  obtain ⟨a,b,hb,he,hv⟩ := h
  refine ⟨b,a, by rw [← hv]; exact mul_ne_zero hy hb, ?_, ?_⟩
  · rw [← he, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · rw [← hv, ← mul_assoc, inv_mul_cancel₀ hy, one_mul]

omit [IsDomain R] in
theorem div (h : RationalAt φ x y) (h' : RationalAt φ x' y') (hy' : y' ≠ 0) :
    RationalAt φ (x/x') (y/y') := by
  simpa only [div_eq_mul_inv] using h.mul (h'.inv hy')

omit [IsDomain R] [IsFractionRing R F] in
theorem pow (h : RationalAt φ x y) (n : ℕ) : RationalAt φ (x^n) (y^n) := by
  induction n with
  | zero => simpa using (one (φ := φ) (F := F))
  | succ n ih => simpa only [pow_succ] using ih.mul h

omit [IsDomain R] [IsFractionRing R F] in
theorem natCast (n : ℕ) : RationalAt φ (n : F) (n : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (n : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem intCast (n : ℤ) : RationalAt φ (n : F) (n : K) := by
  simpa using (algebraMap (φ := φ) (F := F) (n : R))

omit [IsDomain R] [IsFractionRing R F] in
theorem sum {ι : Type*} (s : Finset ι) (f : ι → F) (g : ι → K)
    (h : ∀ i ∈ s, RationalAt φ (f i) (g i)) :
    RationalAt φ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (φ := φ) (F := F))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

omit [IsDomain R] [IsFractionRing R F] in
theorem prod {ι : Type*} (s : Finset ι) (f : ι → F) (g : ι → K)
    (h : ∀ i ∈ s, RationalAt φ (f i) (g i)) :
    RationalAt φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (φ := φ) (F := F))
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end RationalAt
end

 

 

noncomputable section
variable {R F K : Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
  [Algebra R F] [IsFractionRing R F] {φ : R →+* K}

namespace RationalAt

omit [IsDomain R] [IsFractionRing R F] in
theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) : RationalAt φ A.det B.det := by
  classical
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  apply sum
  intro σ _
  exact (intCast _).mul (prod _ _ _ (fun i _ => h (σ i) i))

omit [IsDomain R] [IsFractionRing R F] in
theorem matrixOne {ι : Type*} [DecidableEq ι] (i j : ι) :
    RationalAt φ ((1 : Matrix ι ι F) i j) ((1 : Matrix ι ι K) i j) := by
  classical
  by_cases h : i = j
  · subst j; simpa using (one (φ := φ) (F := F))
  · simpa [Matrix.one_apply, h] using (zero (φ := φ) (F := F))

omit [IsDomain R] [IsFractionRing R F] in
theorem adjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) (i j : ι) :
    RationalAt φ (A.adjugate i j) (B.adjugate i j) := by
  rw [Matrix.adjugate_apply, Matrix.adjugate_apply]
  apply det
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    by_cases hb : b = i
    · subst b; simpa using (one (φ := φ) (F := F))
    · simpa [Pi.single_apply, hb] using (zero (φ := φ) (F := F))
  · simp only [Matrix.updateRow_ne ha]
    exact h a b

omit [IsDomain R] in
theorem nonsingInv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F) (B : Matrix ι ι K)
    (h : ∀ i j, RationalAt φ (A i j) (B i j)) (hB : B.det ≠ 0) (i j : ι) :
    RationalAt φ (A⁻¹ i j) (B⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((det A B h).inv hB).mul (adjugate A B h i j)

omit [IsDomain R] [IsFractionRing R F] in
theorem mulVec {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ F) (B : Matrix ι κ K) (v : κ → F) (w : κ → K)
    (hA : ∀ i j, RationalAt φ (A i j) (B i j))
    (hv : ∀ j, RationalAt φ (v j) (w j)) (i : ι) :
    RationalAt φ (A.mulVec v i) (B.mulVec w i) := by
  apply sum
  intro j _
  exact (hA i j).mul (hv j)

end RationalAt

 

omit [IsDomain R] [IsFractionRing R F] in
theorem rationalAt_column {n : ℕ} (w : Fin n → Weights F) (v : Fin n → Weights K)
    (h : ∀ i t, RationalAt φ ((w i).tile t) ((v i).tile t)) (p q : Pairing n) :
    RationalAt φ (column w p q) (column v p q) := by
  classical
  unfold column
  apply RationalAt.sum
  intro t _
  split_ifs
  · exact RationalAt.prod _ _ _ (fun i _ => h i (t i))
  · exact RationalAt.zero

 

omit [IsDomain R] in
theorem rationalAt_normalizedVacuum {n : ℕ}
    (w : Fin n → Weights F) (v : Fin n → Weights K)
    (h : ∀ i t, RationalAt φ ((w i).tile t) ((v i).tile t))
    (hv : VacuumRegular v) (p : Pairing n) :
    RationalAt φ (normalizedVacuum w p) (normalizedVacuum v p) := by
  classical
  unfold normalizedVacuum attachEmpty
  split_ifs
  · exact RationalAt.one
  · apply RationalAt.mulVec
    · apply RationalAt.nonsingInv
      · intro i j
        exact (RationalAt.matrixOne i j).sub (rationalAt_column w v h i.val j.val)
      · exact hv
    · intro q
      exact rationalAt_column w v h q.val (empty n)

end

 

 

noncomputable section
open Finset

 

def torusCharacter {n k : ℕ} (z : Fin n → SpectralField k) (hz : ∀ i, z i ≠ 0) :
    Multiplicative (Fin n → ℤ) →* SpectralField k where
  toFun e := ∏ i, z i ^ e.toAdd i
  map_one' := by simp
  map_mul' e f := by
    change (∏ i, z i ^ (e.toAdd i + f.toAdd i)) = _
    simp only [zpow_add₀ (hz _), prod_mul_distrib]

def torusEvaluation {n k : ℕ} (z : Fin n → SpectralField k) (hz : ∀ i, z i ≠ 0) :
    Laurent n →ₐ[ℂ] SpectralField k :=
  AddMonoidAlgebra.lift ℂ (SpectralField k) (Fin n → ℤ) (torusCharacter z hz)

@[simp] theorem torusEvaluation_monomial {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (e : Fin n → ℤ) (c : ℂ) :
    torusEvaluation z hz (monomialL e c) = constF k c * ∏ i, z i ^ e i := by
  simp [torusEvaluation, monomialL, AddMonoidAlgebra.lift_single, torusCharacter, constF, Algebra.smul_def]

@[simp] theorem torusEvaluation_constant {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (c : ℂ) :
    torusEvaluation z hz (constantL n c) = constF k c := by
  change torusEvaluation z hz (monomialL 0 c) = _
  simp

@[simp] theorem torusEvaluation_variable {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (i : Fin n) :
    torusEvaluation z hz (monomialL (variableExponent i) 1) = z i := by
  simp [variableExponent, Pi.single_apply, constF]

 

theorem rationalAt_const {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k) (c : ℂ) :
    RationalAt φ.toRingHom (constF n c) (constF k c) := by
  have h := RationalAt.algebraMap (φ := φ.toRingHom) (F := SpectralField n) (constantL n c)
  rw [map_constantL] at h
  have he : φ (constantL n c) = constF k c := φ.commutes c
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, he] using h

theorem rationalAt_variable {n k : ℕ} (z : Fin n → SpectralField k)
    (hz : ∀ i, z i ≠ 0) (i : Fin n) :
    RationalAt (torusEvaluation z hz).toRingHom (variableF i) (z i) := by
  have h := RationalAt.algebraMap (φ := (torusEvaluation z hz).toRingHom)
    (F := SpectralField n) (monomialL (variableExponent i) 1)
  change RationalAt (torusEvaluation z hz).toRingHom (variableF i)
    (torusEvaluation z hz (monomialL (variableExponent i) 1)) at h
  simpa only [torusEvaluation_variable] using h

theorem rationalAt_torusSin {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusSin x) (torusSin z) := by
  have hc : constF k (2*Complex.I) ≠ 0 := by
    apply (map_ne_zero (algebraMap ℂ (SpectralField k))).mpr
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  have hd : RationalAt φ.toRingHom (2 * constF n Complex.I) (2 * constF k Complex.I) :=
    (RationalAt.natCast 2).mul (rationalAt_const φ Complex.I)
  apply (h.sub (h.inv hz)).div hd
  simpa only [constF, map_mul, map_ofNat] using hc

theorem rationalAt_torusCos {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusCos x) (torusCos z) := by
  exact (h.add (h.inv hz)).div (RationalAt.natCast 2) (by exact two_ne_zero)

theorem rationalAt_torusL {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) :
    RationalAt φ.toRingHom (torusL x) (torusL z) := by
  exact (rationalAt_torusSin φ (((rationalAt_const φ phase).pow 2).mul h)
    (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)).mul
    (rationalAt_torusSin φ (((rationalAt_const φ phase).pow 3).mul h)
      (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz))

theorem rationalAt_torusWeights {n k : ℕ} (φ : Laurent n →ₐ[ℂ] SpectralField k)
    {x : SpectralField n} {z : SpectralField k}
    (h : RationalAt φ.toRingHom x z) (hz : z ≠ 0) (hL : torusL z ≠ 0) (t : Tile) :
    RationalAt φ.toRingHom ((torusWeights x).tile t) ((torusWeights z).tile t) := by
  have hq := rationalAt_const φ phase
  have hd := rationalAt_const φ d
  have hs := rationalAt_torusSin φ h hz
  have ht := rationalAt_torusSin φ ((hq.pow 3).div h hz)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)
  have hv := rationalAt_torusSin φ ((hq.pow 2).div h hz)
    (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero k)) hz)
  have hu := rationalAt_torusSin φ (h.div hq (constF_phase_ne_zero k))
    (div_ne_zero hz (constF_phase_ne_zero k))
  have hden := rationalAt_torusL φ h hz
  cases t
  · exact RationalAt.one
  · exact (hd.mul ht).div hden hL
  · exact (hd.mul ht).div hden hL
  · exact (hs.mul ht).div hden hL
  · exact (hs.mul ht).div hden hL
  · exact (hd.mul hs).div hden hL
  · exact (hd.mul hs).div hden hL
  · exact (ht.mul hv).div hden hL
  · exact (hu.mul hs).div hden hL

end

 

 

noncomputable section
open scoped Classical

def copiedNodeWeights {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) :
    Fin (m+1) → Weights (SpectralField n) :=
  Fin.snoc (fun j => spectralWeights n (v j)) (torusWeights (variableF i)⁻¹)

 

theorem copiedNode_regular {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) :
    VacuumRegular (copiedNodeWeights v i) := by
  apply regular_of_cleared_specialization
    (algebraMap (SpectralRing n) (SpectralField n))
    (IsFractionRing.injective (SpectralRing n) (SpectralField n)) (flatEval n).toRingHom
    (Fin.snoc (fun j => rowDenominator (v j)) (inverseRowDenominator i))
    (Fin.snoc (fun j => rowNumerator (v j)) (inverseRowNumerator i))
    (copiedNodeWeights v i) (Fin.snoc (fun _ => deletionWeights) identityWeights)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using inverseRowDenominator_flat_ne_zero i
    | cast j => simpa using flatEval_rowDenominator_ne_zero (v j)
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [evalLaurent,copiedNodeWeights,Fin.snoc_last] using inverseRowNumerator_map i t
    | cast j => simpa only [copiedNodeWeights,Fin.snoc_castSucc] using rowNumerator_map (v j) t
  · intro j t
    induction j using Fin.lastCases with
    | last => simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Fin.snoc_last]
        using inverseRowNumerator_flat i t
    | cast j => simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Fin.snoc_castSucc]
        using rowNumerator_flatEval (v j) t
  · unfold VacuumRegular
    rw [det_one_nonflat]
    · exact one_ne_zero
    · intro j k hj hk
      induction j using Fin.lastCases with
      | last => exact (hj (Or.inl (Fin.snoc_last ..))).elim
      | cast j => exact (hj (Or.inr (Fin.snoc_castSucc ..))).elim

def copyEvaluation {m n : ℕ} (v : Fin m → Fin n) : Laurent m →ₐ[ℂ] SpectralField n :=
  torusEvaluation (fun j => variableF (v j)) (fun j => variableF_ne_zero (v j))

lemma rationalAt_copy_variable {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (variableF i) (variableF (v i)) :=
  rationalAt_variable _ _ i

lemma rationalAt_copy_deletionNode {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (deletionNode i) (deletionNode (v i)) :=
  (rationalAt_copy_variable v i).mul ((rationalAt_const (copyEvaluation v) phase).pow 3)

lemma rationalAt_copy_spectralA {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (spectralA i) (spectralA (v i)) := by
  apply rationalAt_torusCos
  · exact ((rationalAt_copy_variable v i).pow 2).div
      ((rationalAt_const (copyEvaluation v) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero n))
  · exact div_ne_zero (pow_ne_zero _ (variableF_ne_zero (v i))) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma rationalAt_copy_deletionBeta {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (deletionBeta i) (deletionBeta (v i)) := by
  apply rationalAt_torusCos
  · exact ((rationalAt_copy_deletionNode v i).pow 2).div
      ((rationalAt_const (copyEvaluation v) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero n))
  · exact div_ne_zero (pow_ne_zero _ (mul_ne_zero (variableF_ne_zero (v i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma rationalAt_copy_weights {m n : ℕ} (v : Fin m → Fin n) (i : Fin m)
    (j : Fin (m+1)) (t : Tile) :
    RationalAt (copyEvaluation v).toRingHom ((nodalWeights i j).tile t)
      ((copiedNodeWeights v (v i) j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
    simp only [nodalWeights,copiedNodeWeights,Fin.snoc_castSucc,spectralWeights]
    apply rationalAt_torusWeights
    · exact ((rationalAt_const (copyEvaluation v) phase).pow 3).div
        (rationalAt_copy_variable v j) (variableF_ne_zero _)
    · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero _)
    · rw [←rowDenominator_map]
      exact rowDenominator_map_ne_zero _
  | last =>
    simp only [nodalWeights_last,copiedNodeWeights,Fin.snoc_last]
    apply rationalAt_torusWeights
    · exact (rationalAt_copy_variable v i).inv (variableF_ne_zero _)
    · exact inv_ne_zero (variableF_ne_zero _)
    · rw [←inverseRowDenominator_map]
      exact inverseRowDenominator_map_ne_zero _

lemma rationalAt_copy_vacuum {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) (p : Pairing (m+1)) :
    RationalAt (copyEvaluation v).toRingHom
      (normalizedVacuum (nodalWeights i) p)
      (normalizedVacuum (copiedNodeWeights v (v i)) p) :=
  rationalAt_normalizedVacuum _ _ (rationalAt_copy_weights v i) (copiedNode_regular v (v i)) p


 

 


lemma RationalAt.mv_eval {R F K C σ : Type*} [CommRing R] [IsDomain R]
    [Field F] [Field K] [Algebra R F] [IsFractionRing R F] [CommRing C]
    {φ : R →+* K} (c : C →+* F) (d : C →+* K) (v : σ → F) (w : σ → K)
    (hc : ∀ z,RationalAt φ (c z) (d z)) (hv : ∀ i,RationalAt φ (v i) (w i))
    (p : MvPolynomial σ C) :
    RationalAt φ (MvPolynomial.eval₂Hom c v p) (MvPolynomial.eval₂Hom d w p) := by
  induction p using MvPolynomial.induction_on with
  | C z => simpa using hc z
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,MvPolynomial.eval₂Hom_X'] using hp.mul (hv i)

def copiedNodeScalar {m n : ℕ} (v : Fin m → Fin n) (i : Fin n) : SpectralField n :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
    (Fin.snoc (fun j => spectralA (v j)) (deletionBeta i))
    (scalarPolynomial (m+1) d rho (by exact_mod_cast d_ne_zero))

lemma rationalAt_copy_scalar {m n : ℕ} (v : Fin m → Fin n) (i : Fin m) :
    RationalAt (copyEvaluation v).toRingHom (nodalScalar i) (copiedNodeScalar v (v i)) := by
  apply RationalAt.mv_eval
  · exact rationalAt_const (copyEvaluation v)
  · intro j
    induction j using Fin.lastCases with
    | last => simpa using rationalAt_copy_deletionBeta v i
    | cast j => simpa using rationalAt_copy_spectralA v j

lemma rationalAt_copy_nodalVacuum {m n : ℕ} (v : Fin m → Fin n) (i : Fin m)
    (p : Pairing (m+1)) :
    RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p)
      (copiedNodeScalar v (v i)*normalizedVacuum (copiedNodeWeights v (v i)) p) :=
  (rationalAt_copy_scalar v i).mul (rationalAt_copy_vacuum v i p)

 

theorem nodalVacuum_collision {m n : ℕ} (v : Fin m → Fin n) (i j : Fin m)
    (hij:v i=v j) (p : Pairing (m+1)) :
    ∃ y : SpectralField n,
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p) y ∧
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum j p) y := by
  refine ⟨_,rationalAt_copy_nodalVacuum v i p,?_⟩
  rw [hij]
  exact rationalAt_copy_nodalVacuum v j p

 
theorem occupied_nodal_collision {m n : ℕ} (v : Fin m → Fin n) (i j : Fin m)
    (hij:v i=v j) (p : Pairing (m+1)) :
    ∃ y : SpectralField n,
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum i p/torusSin (deletionNode i)) y ∧
      RationalAt (copyEvaluation v).toRingHom (nodalVacuum j p/torusSin (deletionNode j)) y := by
  have hi:=rationalAt_torusSin (copyEvaluation v) (rationalAt_copy_deletionNode v i)
    (mul_ne_zero (variableF_ne_zero (v i)) (pow_ne_zero _ (constF_phase_ne_zero n)))
  have hj:=rationalAt_torusSin (copyEvaluation v) (rationalAt_copy_deletionNode v j)
    (mul_ne_zero (variableF_ne_zero (v j)) (pow_ne_zero _ (constF_phase_ne_zero n)))
  obtain ⟨y,hy,hz⟩:=nodalVacuum_collision v i j hij p
  refine ⟨y/torusSin (deletionNode (v i)),hy.div hi (deletionNode_sine_ne_zero _),?_⟩
  rw [hij]
  exact hz.div hj (deletionNode_sine_ne_zero _)

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

def evalMonomialCharacter (n : ℕ) : Multiplicative (Fin n → ℤ) →* SpectralField n where
  toFun e:=evalLaurent (monomialL e.toAdd 1)
  map_one' := by simp [evalLaurent]
  map_mul' e f:=by
    change evalLaurent (monomialL (e.toAdd+f.toAdd) 1)=_
    simp only [evalLaurent]
    rw [←map_mul]
    simp only [monomialL_mul,mul_one]

lemma evalLaurent_monomial_product {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    evalLaurent (monomialL e z)=constF n z*∏ i,variableF i ^ e i := by
  rw [evalLaurent,map_monomialL_factor]
  congr 1
  have he : e=∑ i:Fin n,(e i) • variableExponent i := by
    funext j
    simp [variableExponent,Pi.single_apply]
  change evalMonomialCharacter n (Multiplicative.ofAdd e)=_
  rw [he]
  simp only [ofAdd_sum,map_prod,ofAdd_zsmul,map_zpow]
  rw [←he]
  rfl

lemma evalLaurent_unit_zpow {n : ℕ} (u : (Laurent n)ˣ) (k : ℤ) :
    evalLaurent ((u^k : (Laurent n)ˣ):Laurent n)=(evalLaurent (u:Laurent n))^k :=
  ((algebraMap (SpectralRing n) (SpectralField n)).toMonoidHom.comp (Units.coeHom _)).map_zpow u k

lemma substituteLaurent_monomial {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    substituteLaurent i u (monomialL e z)=monomialL (Fin.removeNth i e) z * (u^(e i):(Laurent n)ˣ) := by
  change LaurentPolynomial.eval₂ (RingHom.id _) u (peelLaurentEquiv i _)=_
  rw [peelLaurentEquiv_monomial,LaurentPolynomial.single_eq_C_mul_T,LaurentPolynomial.eval₂_C_mul_T]
  rfl

lemma substitution_torusEvaluation {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (v : Fin (n+1) → SpectralField n) (hv:∀ j,v j≠0)
    (hi:v i=evalLaurent (u:Laurent n)) (hj:∀ j,v (i.succAbove j)=variableF j) (f : Laurent (n+1)) :
    torusEvaluation v hv f=evalLaurent (substituteLaurent i u f) := by
  have h:(torusEvaluation v hv).toRingHom=
      (algebraMap (SpectralRing n) (SpectralField n)).comp (substituteLaurent i u) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation v hv (monomialL _ _)=evalLaurent (substituteLaurent i u (monomialL _ _))
    all_goals rw [torusEvaluation_monomial,substituteLaurent_monomial]
    all_goals simp only [evalLaurent,map_mul]
    all_goals rw [←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow]
    all_goals rw [Fin.prod_univ_succAbove _ i]
    all_goals simp only [hi,hj,Fin.removeNth]
    all_goals ring
  exact DFunLike.congr_fun h f

end
end CriticalStrip.Diagram

end OAI
