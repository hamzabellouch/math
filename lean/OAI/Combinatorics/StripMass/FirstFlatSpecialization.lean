import Mathlib
import OAI.Combinatorics.StripMass.ScalarFlat

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

def firstFlatPoint (n : ℕ) : Fin (n+1) → SpectralField n := Fin.cons 1 variableF

lemma firstFlatPoint_ne_zero (n : ℕ) (i : Fin (n+1)) : firstFlatPoint n i ≠ 0 := by
  induction i using Fin.cases with
  | zero => exact one_ne_zero
  | succ i => exact variableF_ne_zero i

def firstFlatEvaluation (n : ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (firstFlatPoint n) (firstFlatPoint_ne_zero n)

lemma rationalAt_firstFlat_variable {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (variableF i) (firstFlatPoint n i) :=
  rationalAt_variable _ _ i

lemma rationalAt_firstFlat_spectralA {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (spectralA i)
      ((Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i) := by
  have h := rationalAt_torusCos (firstFlatEvaluation n)
    (((rationalAt_firstFlat_variable i).pow 2).div
      ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstFlatPoint_ne_zero n i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero => simpa only [firstFlatPoint,Fin.cons_zero,one_pow,one_div,torusCos_inv,
      torusCos_phase_pow,Nat.cast_ofNat,spectralA,c] using h
  | succ i => exact h

lemma rationalAt_firstFlat_deletionNode {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (deletionNode i)
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) := by
  have h := (rationalAt_firstFlat_variable i).mul
    ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
  induction i using Fin.cases with
  | zero => simpa only [firstFlatPoint,Fin.cons_zero,one_mul,deletionNode] using h
  | succ i => exact h

lemma rationalAt_firstFlat_deletionBeta {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (deletionBeta i)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  have hn : (Fin.cons (constF n phase^3) (@deletionNode n) : Fin (n+1) → SpectralField n) i≠0 := by
    induction i using Fin.cases with
    | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
    | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))
  have h:=rationalAt_torusCos (firstFlatEvaluation n)
    (((rationalAt_firstFlat_deletionNode i).pow 2).div
      ((rationalAt_const (firstFlatEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ hn) (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he : (constF n phase^3)^2/constF n phase^3=constF n phase^3 := by
        field_simp
      simpa only [Fin.cons_zero,he,torusCos_phase_pow,Nat.cast_ofNat,deletionBeta,c] using h
  | succ i => exact h

def firstFlatSmallerWeights (n : ℕ) : Fin (n+1) → Fin (n+1) → Weights (SpectralField n) :=
  Fin.cons (Fin.snoc (spectralWeights n) identityWeights) nodalWeights

lemma firstFlatSmaller_regular (n : ℕ) (i : Fin (n+1)) :
    VacuumRegular (firstFlatSmallerWeights n i) := by
  induction i using Fin.cases with
  | zero =>
      unfold VacuumRegular firstFlatSmallerWeights
      simp only [Fin.cons_zero]
      rw [det_flat_top _ (Or.inl (Fin.snoc_last ..))]
      simpa only [firstFlatSmallerWeights,Fin.cons_zero,Fin.snoc_castSucc,VacuumRegular] using spectral_regular n
  | succ i => exact nodal_regular i

lemma rationalAt_firstFlat_nodalWeights {n : ℕ} (i : Fin (n+1))
    (j : Fin (n+2)) (t : Tile) :
    RationalAt (firstFlatEvaluation n).toRingHom ((nodalWeights i j).tile t)
      (((Fin.cons deletionWeights (firstFlatSmallerWeights n i) : Fin (n+2) → Weights (SpectralField n)) j).tile t) := by
  have hq:=rationalAt_const (firstFlatEvaluation n) phase
  induction j using Fin.lastCases with
  | cast j =>
      simp only [nodalWeights,Fin.snoc_castSucc,spectralWeights]
      induction j using Fin.cases with
      | zero =>
          have hv := (hq.pow 3).div (rationalAt_firstFlat_variable 0) one_ne_zero
          simp only [firstFlatPoint,Fin.cons_zero,div_one] at hv
          have h := rationalAt_torusWeights (firstFlatEvaluation n) hv
            (pow_ne_zero 3 (constF_phase_ne_zero n))
            (by rw [torusL_phase_three]; simpa only [torusL_one] using torusL_one_ne_zero n) t
          simpa [torusWeights_phase_three] using h
      | succ j =>
          have hv := (hq.pow 3).div (rationalAt_firstFlat_variable j.succ) (variableF_ne_zero j)
          simp only [firstFlatPoint,Fin.cons_succ] at hv
          have h := rationalAt_torusWeights (firstFlatEvaluation n) hv
            (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero j))
            (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero j) t
          induction i using Fin.cases with
          | zero => simpa [firstFlatSmallerWeights,spectralWeights] using h
          | succ i => simpa [firstFlatSmallerWeights,nodalWeights,spectralWeights] using h
  | last =>
      simp only [nodalWeights_last]
      induction i using Fin.cases with
      | zero =>
          have hv := (rationalAt_firstFlat_variable (0:Fin (n+1))).inv one_ne_zero
          simp only [firstFlatPoint,Fin.cons_zero,inv_one] at hv
          have h:=rationalAt_torusWeights (firstFlatEvaluation n) hv
            one_ne_zero (torusL_one_ne_zero n) t
          simpa only [torusWeights_one,Fin.cons_last,firstFlatSmallerWeights,
            Fin.cons_zero,Fin.snoc_last] using h
      | succ i =>
          have hv := (rationalAt_firstFlat_variable i.succ).inv (variableF_ne_zero i)
          simp only [firstFlatPoint,Fin.cons_succ] at hv
          have h:=rationalAt_torusWeights (firstFlatEvaluation n) hv
            (inv_ne_zero (variableF_ne_zero i))
            (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) t
          simpa only [Fin.cons_last,firstFlatSmallerWeights,Fin.cons_succ,nodalWeights_last] using h

lemma rationalAt_firstFlat_normalizedVacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    RationalAt (firstFlatEvaluation n).toRingHom (normalizedVacuum (nodalWeights i) p)
      (firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
        (normalizedVacuum (firstFlatSmallerWeights n i)) p) := by
  have hr : VacuumRegular (Fin.cons deletionWeights (firstFlatSmallerWeights n i)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact firstFlatSmaller_regular n i
  have h:=rationalAt_normalizedVacuum _ _ (rationalAt_firstFlat_nodalWeights i) hr p
  rw [normalizedVacuum_firstZero _ (firstFlatSmaller_regular n i)] at h
  exact h


 

 


lemma scalarPolynomial_eval_snoc_flat {K : Type*} [Field K] (f : ℂ →+* K)
    (n : ℕ) (a : Fin n → K) :
    MvPolynomial.eval₂Hom f (Fin.snoc a (f (c:ℂ)))
      (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))=
      (∏ i, (a i+f (C:ℂ)))*MvPolynomial.eval₂Hom f a
        (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) := by
  rw [Fin.snoc_eq_cons_rotate]
  change MvPolynomial.eval₂Hom f ((Fin.cons (f (c:ℂ)) a : Fin (n+1) → K) ∘ finRotate (n+1)) _ = _
  rw [scalarPolynomial_eval_reindex,source_scalarPolynomial_flat]

lemma scalarPolynomial_eval_spectral (n : ℕ) :
    MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n)) spectralA
      (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero))=spectralNormalization n := by
  exact scalarPolynomial_eval _ _ _ _ _ _ (spectralA_injective n)
    (fun i j hij => spectralA_discriminant_ne i j hij)

 
def firstFlatSmallerScalar (n : ℕ) (i : Fin (n+1)) : SpectralField n :=
  (Fin.cons ((∏ j : Fin n, (spectralA j+constF n C))*spectralNormalization n)
    nodalScalar : Fin (n+1) → SpectralField n) i

lemma firstFlatSmallerScalar_eq (n : ℕ) (i : Fin (n+1)) :
    firstFlatSmallerScalar n i=
      MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)) := by
  induction i using Fin.cases with
  | zero =>
      simp only [firstFlatSmallerScalar,Fin.cons_zero,constF]
      rw [scalarPolynomial_eval_snoc_flat (algebraMap ℂ (SpectralField n)) n spectralA,scalarPolynomial_eval_spectral]
  | succ i => rfl

lemma rationalAt_firstFlat_nodalScalar {n : ℕ} (i : Fin (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (nodalScalar i)
      ((∏ j : Fin n, (spectralA j+constF n C))*
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i) := by
  have h := RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i))
    (Fin.snoc (Fin.cons (constF n c) spectralA)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i))
    (rationalAt_const (firstFlatEvaluation n))
    (fun j => by
      induction j using Fin.lastCases with
      | last => simpa using rationalAt_firstFlat_deletionBeta i
      | cast j => simpa using rationalAt_firstFlat_spectralA j)
    (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero))
  rw [←Fin.cons_snoc_eq_snoc_cons] at h
  simp only [constF] at h
  rw [source_scalarPolynomial_flat (algebraMap ℂ (SpectralField n)) (n+1)] at h
  rw [Fin.prod_univ_castSucc] at h
  simpa only [nodalScalar,Fin.snoc_castSucc,Fin.snoc_last,constF,firstFlatSmallerScalar_eq] using h

lemma rationalAt_firstFlat_nodalVacuum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    RationalAt (firstFlatEvaluation n).toRingHom (nodalVacuum i p)
      (((∏ j : Fin n, (spectralA j+constF n C))*
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i)*
        firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
          (normalizedVacuum (firstFlatSmallerWeights n i)) p) :=
  (rationalAt_firstFlat_nodalScalar i).mul (rationalAt_firstFlat_normalizedVacuum i p)


 

 


def lastEvaluation {n:ℕ} (z:SpectralField n) (hz:z≠0) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (Fin.snoc variableF z) (fun i => Fin.lastCases (by simpa only [Fin.snoc_last] using hz) (fun j => by simpa only [Fin.snoc_castSucc] using variableF_ne_zero j) i)

lemma lastEvaluation_lift {n:ℕ} (z:SpectralField n) (hz:z≠0) (P:Laurent n) :
    lastEvaluation z hz (liftLaurent P)=evalLaurent P := by
  have he:(lastEvaluation z hz).toRingHom.comp (liftLaurentHom n)=
      algebraMap (SpectralRing n) (SpectralField n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change lastEvaluation z hz (liftLaurent (monomialL _ _))=evalLaurent (monomialL _ _)
    all_goals rw [liftLaurent_monomial,evalLaurent_monomial_product]
    all_goals simp only [lastEvaluation,torusEvaluation_monomial,Fin.prod_univ_castSucc,
      Fin.snoc_castSucc,Fin.snoc_last,zpow_zero,mul_one]
  exact DFunLike.congr_fun he P

lemma rationalAt_last_lift {n:ℕ} (z:SpectralField n) (hz:z≠0) (x:SpectralField n) :
    RationalAt (lastEvaluation z hz).toRingHom (liftSpectral n x) x := by
  obtain ⟨a,b,hb,rfl⟩:=IsFractionRing.div_surjective (SpectralRing n) x
  have ha:=RationalAt.algebraMap (φ:=(lastEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (liftLaurent a)
  have hc:=RationalAt.algebraMap (φ:=(lastEvaluation z hz).toRingHom) (F:=SpectralField (n+1)) (liftLaurent b)
  change RationalAt _ (evalLaurent (liftLaurent a)) (lastEvaluation z hz (liftLaurent a)) at ha
  change RationalAt _ (evalLaurent (liftLaurent b)) (lastEvaluation z hz (liftLaurent b)) at hc
  rw [lastEvaluation_lift] at ha hc
  change RationalAt _ (liftSpectral n (evalLaurent a / evalLaurent b)) (evalLaurent a / evalLaurent b)
  rw [map_div₀,liftSpectral_evalLaurent,liftSpectral_evalLaurent]
  exact ha.div hc (map_ne_zero_of_mem_nonZeroDivisors
    (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _) hb)

lemma rationalAt_last_variable {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (variableF (Fin.last n)) z := by
  simpa only [lastEvaluation,Fin.snoc_last] using rationalAt_variable (Fin.snoc variableF z)
    (fun i => Fin.lastCases (by simpa only [Fin.snoc_last] using hz) (fun j => by simpa only [Fin.snoc_castSucc] using variableF_ne_zero j) i) (Fin.last n)

lemma rationalAt_last_spectralA {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (spectralA (Fin.last n))
      (torusCos (z^2/constF n phase^3)) :=
  rationalAt_torusCos (lastEvaluation z hz)
    (((rationalAt_last_variable z hz).pow 2).div ((rationalAt_const _ phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ hz) (pow_ne_zero _ (constF_phase_ne_zero n)))

lemma rationalAt_last_interpolant {n:ℕ} (z:SpectralField n) (hz:z≠0) (p:Pairing (n+1)) :
    RationalAt (lastEvaluation z hz).toRingHom (rationalInterpolant n p)
      (lastValue (RingHom.id _) (torusCos (z^2/constF n phase^3)) (torusSin z)
        (rationalNodalPolynomial n) p) := by
  have he:=RationalAt.eval₂ (lastEvaluation z hz).toRingHom (liftSpectral n) (RingHom.id _)
    (rationalAt_last_lift z hz) (rationalAt_last_spectralA z hz) (rationalNodalPolynomial n p)
  unfold rationalInterpolant lastValue
  split_ifs
  · exact (rationalAt_torusSin _ (rationalAt_last_variable z hz) hz).mul he
  · simpa only [one_mul] using he

lemma rationalAt_last_weights {n:ℕ} (z:SpectralField n) (hz:z≠0)
    (hL:torusL (constF n phase^3/z)≠0) (i:Fin (n+1)) (t:Tile) :
    RationalAt (lastEvaluation z hz).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z)) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  induction i using Fin.lastCases with
  | cast i =>
      simpa only [liftSpectral_weights_tile,Fin.snoc_castSucc] using
        rationalAt_last_lift z hz ((spectralWeights n i).tile t)
  | last =>
      simpa only [spectralWeights,Fin.snoc_last] using rationalAt_torusWeights (lastEvaluation z hz)
        (((rationalAt_const _ phase).pow 3).div (rationalAt_last_variable z hz) hz)
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) hz) hL t

end

 

 

noncomputable section
open Finset

theorem sum_selectedPairs {R : Type*} [AddCommMonoid R] {n : ℕ}
    (D : Fin n → Fin n → R) (hD : ∀ i j, D i j = D j i)
    (σ : Equiv.Perm (Fin n)) :
    (∑ e ∈ selectedPairs σ, D e.val.1 e.val.2) =
      ∑ i : Fin (n/2), D (σ (pairFirst n i)) (σ (pairSecond n i)) := by
  rw [selectedPairs, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    exact upperPair_value D hD _ _ _
  · exact fun i _ j _ h => permutationPair_injective σ h

 

theorem clearedPfaffianTerm_degree {n m : ℕ} (k : Fin m)
    (N D : Matrix (Fin n) (Fin n) (CosineRing m))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, MvPolynomial.degreeOf k (N i j) ≤ w i j)
    (hD : ∀ i j, MvPolynomial.degreeOf k (D i j) ≤ w i j)
    (σ : Equiv.Perm (Fin n)) :
    MvPolynomial.degreeOf k (clearedPfaffianTerm N D σ) ≤
      ∑ e : UpperPair n, w e.val.1 e.val.2 := by
  unfold clearedPfaffianTerm
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  refine (add_le_add ((MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun i _ => hN _ _)))
    ((MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun e _ => hD _ _)))).trans ?_
  rw [← sum_selectedPairs w hw σ, Finset.sum_add_sum_compl]

 
theorem clearedPfaffian_degree {n m : ℕ} (k : Fin m) (t : ℂ)
    (N D : Matrix (Fin n) (Fin n) (CosineRing m))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, MvPolynomial.degreeOf k (N i j) ≤ w i j)
    (hD : ∀ i j, MvPolynomial.degreeOf k (D i j) ≤ w i j) :
    MvPolynomial.degreeOf k (clearedPfaffian (MvPolynomial.C t) N D) ≤
      ∑ e : UpperPair n, w e.val.1 e.val.2 := by
  unfold clearedPfaffian
  apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro σ _
  have hs : ((Equiv.Perm.sign σ : ℤ) : CosineRing m) =
      MvPolynomial.C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by simp
  rw [hs]
  exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    (clearedPfaffianTerm_degree k N D w hw hN hD σ)

theorem numerator_degree_bound {n : ℕ} (k : Fin n) (rr : ℂ)
    (a b : CosineRing n) (r : ℕ)
    (ha : MvPolynomial.degreeOf k a ≤ r) (hb : MvPolynomial.degreeOf k b ≤ r) :
    MvPolynomial.degreeOf k ((a-b)*(a+b+MvPolynomial.C rr)) ≤ 2*r := by
  have h₁ : MvPolynomial.degreeOf k (a-b) ≤ r :=
    (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ha hb)
  have h₂ : MvPolynomial.degreeOf k (a+b+MvPolynomial.C rr) ≤ r := by
    refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ha hb)
    · simp
  exact (MvPolynomial.degreeOf_mul_le _ _ _).trans (by omega)

theorem discriminant_degree_bound {n : ℕ} (k : Fin n) (dd : ℂ)
    (a b : CosineRing n) (r : ℕ)
    (ha : MvPolynomial.degreeOf k a ≤ r) (hb : MvPolynomial.degreeOf k b ≤ r) :
    MvPolynomial.degreeOf k (discriminant (MvPolynomial.C dd) a b) ≤ 2*r := by
  have he : discriminant (MvPolynomial.C dd) a b =
      a^2+b^2+MvPolynomial.C (2*dd)*(a*b)-MvPolynomial.C (dd^2) := by
    simp only [discriminant, map_mul, map_ofNat, map_pow]
    ring
  rw [he]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  swap
  · simpa only [MvPolynomial.degreeOf_C] using
      (Nat.zero_le (2*r))
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.degreeOf_pow_le _ _ 2).trans (Nat.mul_le_mul_left 2 ha)
    · exact (MvPolynomial.degreeOf_pow_le _ _ 2).trans (Nat.mul_le_mul_left 2 hb)
  · exact (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
      ((MvPolynomial.degreeOf_mul_le _ _ _).trans (by omega))

 

def scalarEdgeDegree {n : ℕ} (k : Fin n) (i j : Fin (n+n%2)) : ℕ :=
  if i.val < n ∧ j.val < n ∧ (i.val = k.val ∨ j.val = k.val) then 2 else 0

theorem scalarEdgeDegree_symm {n : ℕ} (k : Fin n) (i j : Fin (n+n%2)) :
    scalarEdgeDegree k i j = scalarEdgeDegree k j i := by
  unfold scalarEdgeDegree
  congr 1
  apply propext
  tauto

theorem augmentedNumerator_degree {n : ℕ} (k : Fin n) (rr : ℂ) (i j : Fin (n+n%2)) :
    MvPolynomial.degreeOf k (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X i j) ≤
      scalarEdgeDegree k i j := by
  unfold augmentedNumerator scalarEdgeDegree
  split_ifs with hi hj hd <;> try simp_all
  · apply numerator_degree_bound k rr _ _ 1 <;>
      simp only [MvPolynomial.degreeOf_X] <;> split_ifs <;> omega
  · have hki : k ≠ (⟨i.val,hi⟩ : Fin n) := by intro h; exact hd.1 (congrArg Fin.val h).symm
    have hkj : k ≠ (⟨j.val,hj⟩ : Fin n) := by intro h; exact hd.2 (congrArg Fin.val h).symm
    simpa using numerator_degree_bound k rr (MvPolynomial.X ⟨i.val,hi⟩) (MvPolynomial.X ⟨j.val,hj⟩) 0 (by simp [MvPolynomial.degreeOf_X, hki])
      (by simp [MvPolynomial.degreeOf_X, hkj])

theorem augmentedDenominator_degree {n : ℕ} (k : Fin n) (dd : ℂ) (i j : Fin (n+n%2)) :
    MvPolynomial.degreeOf k (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X i j) ≤
      scalarEdgeDegree k i j := by
  unfold augmentedDenominator scalarEdgeDegree
  split_ifs with hi hj hd <;> try simp_all
  · apply discriminant_degree_bound k dd _ _ 1 <;>
      simp only [MvPolynomial.degreeOf_X] <;> split_ifs <;> omega
  · have hki : k ≠ (⟨i.val,hi⟩ : Fin n) := by intro h; exact hd.1 (congrArg Fin.val h).symm
    have hkj : k ≠ (⟨j.val,hj⟩ : Fin n) := by intro h; exact hd.2 (congrArg Fin.val h).symm
    simpa using discriminant_degree_bound k dd (MvPolynomial.X ⟨i.val,hi⟩) (MvPolynomial.X ⟨j.val,hj⟩) 0 (by simp [MvPolynomial.degreeOf_X, hki])
      (by simp [MvPolynomial.degreeOf_X, hkj])


 

 


def incidentPair {n : ℕ} (k : Fin n) (j : {j : Fin n // j ≠ k}) : UpperPair n :=
  upperPair k j.val j.property.symm

theorem incidentPair_injective {n : ℕ} (k : Fin n) : Function.Injective (incidentPair k) := by
  intro j l h
  rcases (upperPair_eq_iff _ _).mp h with h | h
  · exact Subtype.ext h.2
  · exact False.elim (j.property h.2)

theorem incidentPair_has_k {n : ℕ} (k : Fin n) (j : {j : Fin n // j ≠ k}) :
    (incidentPair k j).val.1 = k ∨ (incidentPair k j).val.2 = k := by
  unfold incidentPair upperPair
  split_ifs <;> simp

theorem incidentPair_range {n : ℕ} (k : Fin n) (e : UpperPair n) :
    e ∈ Set.range (incidentPair k) ↔ e.val.1 = k ∨ e.val.2 = k := by
  constructor
  · rintro ⟨j,rfl⟩
    exact incidentPair_has_k k j
  · rintro (h | h)
    · refine ⟨⟨e.val.2, by rw [← h]; exact ne_of_gt e.property⟩,?_⟩
      simp only [incidentPair, upperPair, ← h, e.property, dite_true]
    · refine ⟨⟨e.val.1, by rw [← h]; exact ne_of_lt e.property⟩,?_⟩
      have he : ¬ e.val.2 < e.val.1 := not_lt_of_ge e.property.le
      simp only [incidentPair, upperPair, ← h, he, dite_false]

theorem sum_incident_degree {n : ℕ} (k : Fin n) (r : ℕ) :
    (∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then r else 0) = r*(n-1) := by
  have hc : Fintype.card {j : Fin n // j ≠ k} = n-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  have hs : (∑ j : {j : Fin n // j ≠ k}, r) =
      ∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then r else 0 := by
    apply Fintype.sum_of_injective (incidentPair k) (incidentPair_injective k)
    · intro e he
      simp only [incidentPair_range] at he
      simp [he]
    · intro j
      simp [incidentPair_has_k]
  simpa [hc, mul_comm] using hs.symm

theorem sum_scalarEdgeDegree {n : ℕ} (k : Fin n) :
    (∑ e : UpperPair (n+n%2), scalarEdgeDegree k e.val.1 e.val.2) = 2*(n-1) := by
  let hn : n ≤ n+n%2 := Nat.le_add_right _ _
  have hs : (∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then 2 else 0) =
      ∑ e : UpperPair (n+n%2), scalarEdgeDegree k e.val.1 e.val.2 := by
    apply Fintype.sum_of_injective (upperPairEmbed hn) (upperPairEmbed_injective hn)
    · intro e he
      unfold scalarEdgeDegree
      split_ifs with h
      · exfalso
        apply he
        refine ⟨⟨(⟨e.val.1.val,h.1⟩,⟨e.val.2.val,h.2.1⟩),e.property⟩,?_⟩
        apply Subtype.ext
        exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
      · rfl
    · intro e
      simp [scalarEdgeDegree, upperPairEmbed, e.val.1.isLt, e.val.2.isLt, Fin.ext_iff]
  rw [← hs]
  exact sum_incident_degree k 2

theorem scalarNumerator_degree (n : ℕ) (dd rr : ℂ) (k : Fin n) :
    MvPolynomial.degreeOf k (scalarNumerator n dd rr) ≤ 2*(n-1) := by
  rw [← sum_scalarEdgeDegree k]
  exact clearedPfaffian_degree k _ _ _ (scalarEdgeDegree k) (scalarEdgeDegree_symm k)
    (augmentedNumerator_degree k rr) (augmentedDenominator_degree k dd)


 

 


 

theorem coeff_prod_budget {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (P : ι → Polynomial R) (w : ι → ℕ)
    (hP : ∀ i ∈ s, (P i).natDegree ≤ w i) :
    (∏ i ∈ s, P i).coeff (∑ i ∈ s, w i) = ∏ i ∈ s, (P i).coeff (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.prod_insert hi]
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hP i (by simp))]
    · rw [ih (fun j hj => hP j (by simp [hj]))]
    · exact (Polynomial.natDegree_prod_le s P).trans
        (Finset.sum_le_sum (fun j hj => hP j (by simp [hj])))

 

theorem clearedPfaffianTerm_top {R : Type*} [CommRing R] {n : ℕ}
    (N D : Matrix (Fin n) (Fin n) (Polynomial R))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, (N i j).natDegree ≤ w i j)
    (hD : ∀ i j, (D i j).natDegree ≤ w i j)
    (σ : Equiv.Perm (Fin n)) :
    (clearedPfaffianTerm N D σ).coeff (∑ e : UpperPair n, w e.val.1 e.val.2) =
      clearedPfaffianTerm (fun i j => (N i j).coeff (w i j))
        (fun i j => (D i j).coeff (w i j)) σ := by
  have hs : (∑ e : UpperPair n, w e.val.1 e.val.2) =
      (∑ i : Fin (n/2), w (σ (pairFirst n i)) (σ (pairSecond n i))) +
        ∑ e ∈ (selectedPairs σ)ᶜ, w e.val.1 e.val.2 := by
    rw [← sum_selectedPairs w hw σ,Finset.sum_add_sum_compl]
  rw [clearedPfaffianTerm,hs,Polynomial.coeff_mul_add_eq_of_natDegree_le]
  · rw [coeff_prod_budget _ _ _ (fun i _ => hN _ _),
      coeff_prod_budget _ _ _ (fun i _ => hD _ _)]
    rfl
  · exact (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hN _ _))
  · exact (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hD _ _))

theorem clearedPfaffian_top {R : Type*} [CommRing R] {n : ℕ} (t : R)
    (N D : Matrix (Fin n) (Fin n) (Polynomial R))
    (w : Fin n → Fin n → ℕ) (hw : ∀ i j, w i j = w j i)
    (hN : ∀ i j, (N i j).natDegree ≤ w i j)
    (hD : ∀ i j, (D i j).natDegree ≤ w i j) :
    (clearedPfaffian (Polynomial.C t) N D).coeff (∑ e : UpperPair n, w e.val.1 e.val.2) =
      clearedPfaffian t (fun i j => (N i j).coeff (w i j))
        (fun i j => (D i j).coeff (w i j)) := by
  unfold clearedPfaffian
  rw [Polynomial.coeff_C_mul,Polynomial.finsetSum_coeff,mul_sum]
  symm
  rw [mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  have he : ((Equiv.Perm.sign σ : ℤ) : Polynomial R) =
      Polynomial.C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [he,Polynomial.coeff_C_mul,clearedPfaffianTerm_top N D w hw hN hD σ]

end
end CriticalStrip.Diagram

end OAI
