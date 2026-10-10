import Mathlib
import OAI.Combinatorics.StripMass.VacuumClosure

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators
theorem polynomialNorthSource_merge (n : ℕ) (p : SourcePairing (n+2)) :
    pairEvaluation n 2 (polynomialNorthSource (n+2) p) =
      mergePairScalar n *
        (sourceBlock (mergeMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => mergeEvaluation n (polynomialNorthSource (n+1) q)) p := by
  let P := (vacuumData (n+2)).P
  let Q := (vacuumData (n+1)).P
  let M : Matrix (Pairing (n+3)) (Pairing (n+2)) (SpectralField (n+1)) :=
    mergeMap 0 (by omega)
  have he := rationalNodalPolynomial_pair_merge (polynomialVacuumVector (n+1))
    (polynomialVacuumVector_eval (n+1)) Q (vacuumData (n+1)).map_P
    (vacuumData (n+1)).eval_P P (vacuumData (n+2)).map_P
  have hM : LastMatrix M := mergeMap_last 0 (show 2≤n+2 by omega)
  let Q' := fun q => (Q q).map (mergeEvaluation n).toRingHom
  have hQ : LastDegree (n+1) (matrixPolynomial M Q') :=
    hM.degree Q' (((vacuumData (n+1)).degree).map (mergeEvaluation n).toRingHom)
  have hh := congrArg (fun U : Pairing (n+3) → Polynomial (SpectralField (n+1)) =>
    (U p.val).coeff (n+1)) he
  change ((P p.val).map _).coeff (n+1) =
    (mergePairPolynomial n * matrixPolynomial M Q' p.val).coeff (n+1) at hh
  have ht := LastDegree.occupied_mul_top _ hQ _ (mergePairPolynomial_degree n) _
      p.property (by omega : 1 ≤ n+1)
  simp only [Nat.add_sub_cancel] at ht
  rw [ht, mergePairPolynomial_top, hM.source_coeff] at hh
  simp only [Polynomial.coeff_map] at hh
  unfold polynomialNorthSource
  simp only [map_mul]
  
  have hc : pairEvaluation n 2 (constantL (n+2) (1/(2*(d:ℂ)))) =
      mergeEvaluation n (constantL (n+1) (1/(2*(d:ℂ)))) := by
    change pairEvaluation n 2 (algebraMap ℂ (Laurent (n+2)) _) =
      mergeEvaluation n (algebraMap ℂ (Laurent (n+1)) _)
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [hc]
  simp only [Nat.add_sub_cancel, show n+2-1=n+1 by omega]
  change _ * (pairEvaluation n 2 ((P p.val).coeff (n+1))) = _
  have hh' : pairEvaluation n 2 ((P p.val).coeff (n+1)) =
    mergePairScalar n * (sourceBlock M).mulVec
      (fun q => (Q' q.val).coeff n) p := hh
  rw [hh']
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Q', Polynomial.coeff_map]

  apply Finset.sum_congr rfl
  intro q _
  change _ * (_ * (sourceBlock M p q * (mergeEvaluation n ((Q q.val).coeff n)))) =
    _ * (sourceBlock M p q * (_ * (mergeEvaluation n ((Q q.val).coeff n))))
  ring

 

theorem polynomialNorthSource_delete (n : ℕ) (p : SourcePairing (n+2)) :
    pairEvaluation n 3 (polynomialNorthSource (n+2) p) =
      deletePairScalar n *
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (polynomialNorthSource n q)) p := by
  let P := (vacuumData (n+2)).P
  let Q := (vacuumData n).P
  let M : Matrix (Pairing (n+3)) (Pairing (n+1)) (SpectralField (n+1)) :=
    deletionMap 0 (by omega)
  have he := rationalNodalPolynomial_pair_delete (polynomialVacuumVector (n+1))
    (polynomialVacuumVector_eval (n+1)) Q (vacuumData n).map_P
    (vacuumData n).eval_P P (vacuumData (n+2)).map_P
  have hM : LastMatrix M := deletionMap_last 0 (show 2≤n+2 by omega)
  let Q' := fun q => (Q q).map (deleteEvaluation n).toRingHom
  have hQ : LastDegree n (matrixPolynomial M Q') :=
    hM.degree Q' (((vacuumData n).degree).map (deleteEvaluation n).toRingHom)
  have hh := congrArg (fun U : Pairing (n+3) → Polynomial (SpectralField (n+1)) =>
    (U p.val).coeff (n+1)) he
  change ((P p.val).map _).coeff (n+1) =
    (deletePairPolynomial n * matrixPolynomial M Q' p.val).coeff (n+1) at hh
  have ht : (deletePairPolynomial n * matrixPolynomial M Q' p.val).coeff (n+1) =
      deletePairScalar n * (sourceBlock M).mulVec (fun q => (Q' q.val).coeff (n-1)) p := by
    by_cases hn : 1 ≤ n
    · have ht := LastDegree.occupied_mul_top _ hQ _ (deletePairPolynomial_degree n) _
        p.property hn
      have hn' : n+2-1=n+1 := by omega
      rw [hn', deletePairPolynomial_top, hM.source_coeff] at ht
      exact ht
    · have hn : n=0 := by omega
      have hz : matrixPolynomial M Q' p.val=0 := by
        apply Polynomial.ext
        intro k
        rw [Polynomial.coeff_zero]
        exact hQ p.val k (by simp [p.property, hn])
      rw [hz, mul_zero, Polynomial.coeff_zero]
      have hne : IsEmpty (SourcePairing n) := hn ▸ isEmpty_source_zero
      let := hne
      simp [Matrix.mulVec, dotProduct]
  rw [ht, Polynomial.coeff_map] at hh
  have hh' : pairEvaluation n 3 ((P p.val).coeff (n+1)) =
      deletePairScalar n * (sourceBlock M).mulVec (fun q => (Q' q.val).coeff (n-1)) p := hh
  unfold polynomialNorthSource
  simp only [map_mul]
  have hc : pairEvaluation n 3 (constantL (n+2) (1/(2*(d:ℂ)))) =
      deleteEvaluation n (constantL n (1/(2*(d:ℂ)))) := by
    change pairEvaluation n 3 (algebraMap ℂ (Laurent (n+2)) _) =
      deleteEvaluation n (algebraMap ℂ (Laurent n) _)
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [hc]
  simp only [show n+2-1=n+1 by omega]
  change _ * (pairEvaluation n 3 ((P p.val).coeff (n+1))) = _
  rw [hh']
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Q', Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro q _
  change _ * (_ * (sourceBlock M p q * (deleteEvaluation n ((Q q.val).coeff (n-1))))) =
    _ * (sourceBlock M p q * (_ * (deleteEvaluation n ((Q q.val).coeff (n-1)))))
  ring



 


 
def reflectionMonomial (n : ℕ) : Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (-e.toAdd) (phase ^ (3 * ∑ i, e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (-(e.toAdd+f.toAdd))
        (phase ^ (3 * ∑ i, (e.toAdd i+f.toAdd i))) = _
    rw [Finset.sum_add_distrib, mul_add, zpow_add₀ phase_ne_zero, neg_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def reflectLaurent (n : ℕ) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (reflectionMonomial n)).toRingHom

@[simp] lemma reflectLaurent_monomial {n : ℕ} (e : Fin n → ℤ) (z : ℂ) :
    reflectLaurent n (monomialL e z) = monomialL (-e) (z * phase ^ (3 * ∑ i, e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (reflectionMonomial n) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single (-e) _ = AddMonoidAlgebra.single (-e) _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]
  rfl

lemma reflectLaurent_involutive (n : ℕ) : Function.Involutive (reflectLaurent n) := by
  have h : (reflectLaurent n).comp (reflectLaurent n) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (reflectLaurent n (monomialL _ _)) = monomialL _ _
    all_goals rw [reflectLaurent_monomial, reflectLaurent_monomial]
    all_goals simp only [neg_neg, Pi.neg_apply, Finset.sum_neg_distrib, mul_neg,
      mul_assoc, ←zpow_add₀ phase_ne_zero, add_neg_cancel, zpow_zero, mul_one]
  intro f
  exact DFunLike.congr_fun h f

def reflectSpectral (n : ℕ) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (reflectLaurent n))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (reflectLaurent_involutive n).injective)

@[simp] lemma reflectSpectral_evalLaurent {n : ℕ} (f : Laurent n) :
    reflectSpectral n (evalLaurent f) = evalLaurent (reflectLaurent n f) :=
  IsFractionRing.lift_algebraMap _ _

lemma reflectSpectral_involutive (n : ℕ) : Function.Involutive (reflectSpectral n) := by
  have h : (reflectSpectral n).comp (reflectSpectral n) = RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (reflectSpectral n (evalLaurent f)) = evalLaurent f
    rw [reflectSpectral_evalLaurent, reflectSpectral_evalLaurent, reflectLaurent_involutive]
  intro f
  exact DFunLike.congr_fun h f

@[simp] lemma reflectSpectral_const (n : ℕ) (z : ℂ) :
    reflectSpectral n (constF n z) = constF n z := by
  have hc : constF n z = evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc, reflectSpectral_evalLaurent]
  change evalLaurent (reflectLaurent n (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [reflectLaurent_monomial]
  simp

@[simp] lemma reflectSpectral_variable {n : ℕ} (i : Fin n) :
    reflectSpectral n (variableF i) = constF n phase ^ 3 / variableF i := by
  change reflectSpectral n (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [reflectSpectral_evalLaurent, reflectLaurent_monomial]
  simp only [variableExponent, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, one_mul, mul_one]
  change evalLaurent (monomialL (-variableExponent i) (phase^3)) = _
  rw [evalLaurent, map_monomialL_neg_variable]
  simp [constF, div_eq_mul_inv]

@[simp] lemma reflectSpectral_torusSin {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusSin z) = torusSin (reflectSpectral n z) := by
  simp [torusSin, map_div₀, map_inv₀, map_ofNat]

@[simp] lemma reflectSpectral_torusCos {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusCos z) = torusCos (reflectSpectral n z) := by
  simp [torusCos, map_div₀, map_inv₀, map_ofNat]

@[simp] lemma reflectSpectral_torusL {n : ℕ} (z : SpectralField n) :
    reflectSpectral n (torusL z) = torusL (reflectSpectral n z) := by simp [torusL]

@[simp] lemma reflectSpectral_torusWeights {n : ℕ} (z : SpectralField n) :
    (torusWeights z).map (reflectSpectral n) = torusWeights (reflectSpectral n z) := by
  simp [Weights.map, torusWeights, map_div₀]

@[simp] lemma reflectSpectral_spectralA {n : ℕ} (i : Fin n) :
    reflectSpectral n (spectralA i) = spectralA i := by
  simp only [spectralA, reflectSpectral_torusCos, map_div₀, map_pow,
    reflectSpectral_const, reflectSpectral_variable]
  unfold torusCos
  field_simp [variableF_ne_zero, constF_phase_ne_zero]
  ring

@[simp] lemma reflectSpectral_normalization (n : ℕ) :
    reflectSpectral n (spectralNormalization n) = spectralNormalization n := by
  simp only [spectralNormalization, map_scalarNormalization, reflectSpectral_const,
    reflectSpectral_spectralA]

lemma reflectLaurent_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Laurent n) :
    reflectLaurent n (permLaurent σ f) = permLaurent σ (reflectLaurent n f) := by
  have h : (reflectLaurent n).comp (permLaurent σ) =
      (permLaurent σ).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (permLaurent σ (monomialL _ _)) =
      permLaurent σ (reflectLaurent n (monomialL _ _))
    all_goals rw [permLaurent_monomial, reflectLaurent_monomial,
      reflectLaurent_monomial, permLaurent_monomial]
    all_goals simp only [Function.comp_apply, Equiv.sum_comp]
    all_goals rfl
  exact DFunLike.congr_fun h f

lemma reflectSpectral_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : SpectralField n) :
    reflectSpectral n (permSpectral σ f) = permSpectral σ (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (permSpectral σ) =
      (permSpectral σ).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (permSpectral σ (evalLaurent f)) =
      permSpectral σ (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent, permSpectral_evalLaurent, reflectLaurent_perm]
  exact DFunLike.congr_fun h f

lemma reflectLaurent_sign {n : ℕ} (i : Fin n) (f : Laurent n) :
    reflectLaurent n (signLaurent i f) = signLaurent i (reflectLaurent n f) := by
  have h : (reflectLaurent n).comp (signLaurent i) =
      (signLaurent i).comp (reflectLaurent n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change reflectLaurent n (signLaurent i (monomialL _ _)) =
      signLaurent i (reflectLaurent n (monomialL _ _))
    all_goals rw [signLaurent_monomial, reflectLaurent_monomial,
      reflectLaurent_monomial, signLaurent_monomial]
    all_goals simp only [Pi.neg_apply, zpow_neg, ←inv_zpow, inv_neg_one]; congr 1; ring
  exact DFunLike.congr_fun h f

lemma reflectSpectral_sign {n : ℕ} (i : Fin n) (f : SpectralField n) :
    reflectSpectral n (signSpectral i f) = signSpectral i (reflectSpectral n f) := by
  have h : (reflectSpectral n).comp (signSpectral i) =
      (signSpectral i).comp (reflectSpectral n) := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change reflectSpectral n (signSpectral i (evalLaurent f)) =
      signSpectral i (reflectSpectral n (evalLaurent f))
    simp only [reflectSpectral_evalLaurent, signSpectral_evalLaurent, reflectLaurent_sign]
  exact DFunLike.congr_fun h f

lemma LaurentBox.reflect {n : ℕ} {f : Laurent n} {b : Fin n → ℕ}
    (hf : LaurentBox f b) : LaurentBox (reflectLaurent n f) b := by
  rw [←AddMonoidAlgebra.sum_coeff_single f]
  change LaurentBox (reflectLaurent n (∑ e ∈ f.coeff.support, monomialL e (f.coeff e))) b
  rw [map_sum]
  apply LaurentBox.sum
  intro e he
  rw [reflectLaurent_monomial]
  apply LaurentBox.single
  intro i
  have hh := hf e (Finsupp.mem_support_iff.mp he) i
  simp only [Pi.neg_apply]
  omega



 


lemma sourceBlock_map {K L : Type*} {n m : ℕ} (f : K → L)
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    (sourceBlock M).map f = sourceBlock (M.map f) := rfl

lemma sourceBlock_transpose {K : Type*} {n m : ℕ}
    (M : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    sourceBlock M.transpose = (sourceBlock M).transpose := rfl

lemma LastMatrix.source_mul {K : Type*} [CommRing K] {n m r : ℕ}
    {M : Matrix (Pairing (r+1)) (Pairing (m+1)) K} (hM : LastMatrix M)
    (N : Matrix (Pairing (m+1)) (Pairing (n+1)) K) :
    sourceBlock (M*N) = sourceBlock M * sourceBlock N := by
  ext p q
  exact hM.source_mulVec (fun a => N a q.val) p

lemma glueMatrix_last {K : Type*} [Zero K] [One K] (n : ℕ) :
    LastMatrix (glueMatrix (Fin.last n) : Matrix _ _ K) := by
  intro p q h
  apply ite_eq_right
  intro hg
  exact h (hg.2.1 _)

lemma LastMatrix.transpose {K : Type*} [Zero K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M) :
    LastMatrix M.transpose := by
  intro p q h
  exact hM q p (fun hh => h hh.symm)

 
def sourceGlue {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) : K :=
  v ⬝ᵥ (sourceBlock (glueMatrix (Fin.last n))).mulVec w

lemma sourceGlue_symmetric {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) : sourceGlue n v w = sourceGlue n w v := by
  unfold sourceGlue
  rw [Matrix.dotProduct_mulVec, ←glueMatrix_transpose (Fin.last n),
    sourceBlock_transpose,Matrix.vecMul_transpose, dotProduct_comm]
  rw [← sourceBlock_transpose, glueMatrix_transpose]

lemma sourceGlue_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (n : ℕ) (v w : SourcePairing n → K) :
    f (sourceGlue n v w) = sourceGlue n (f ∘ v) (f ∘ w) := by
  simp only [sourceGlue, dotProduct, Matrix.mulVec, map_sum, map_mul,
    sourceBlock, glueMatrix, Function.comp_apply, apply_ite, map_one, map_zero]

lemma sourceGlue_adjoint {K : Type*} [CommRing K] {n : ℕ}
    (a : Position n) (w : Weights K) (v z : SourcePairing n → K) :
    sourceGlue n v ((sourceBlock (localR a.padTop w)).mulVec z) =
      sourceGlue n ((sourceBlock (localR a.padTop w)).mulVec v) z := by
  have ha : Fin.last n ≠ a.padTop.left := by
    intro he
    have hh := congrArg Fin.val he
    have := a.left.isLt
    simp only [Position.padTop, Fin.val_last, Fin.val_castSucc] at hh
    omega
  have hb : Fin.last n ≠ a.padTop.right := by
    intro he
    have hh := congrArg Fin.val he
    have := a.right.isLt
    simp only [Position.padTop, Fin.val_last, Fin.val_castSucc] at hh
    omega
  have h := congrArg sourceBlock (localR_glue_adjoint a.padTop (Fin.last n) ha hb w)
  rw [(glueMatrix_last n).source_mul, (LastMatrix.local a w).transpose.source_mul,
    sourceBlock_transpose] at h
  unfold sourceGlue
  rw [Matrix.mulVec_mulVec, h, ←Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma polynomialNorthSource_eval_numerator (n : ℕ) (p : SourcePairing n) :
    evalLaurent (polynomialNorthSource n p) =
      constF n (1/(2*(d:ℂ))) * northNumerator n p := by
  unfold polynomialNorthSource evalLaurent
  rw [map_mul, map_constantL, ←Polynomial.coeff_map, (vacuumData n).map_P]
  rfl

lemma polynomialNorthSource_covariance {n : ℕ} (r : ℕ) (hr : r+2≤n) :
    (fun p => evalLaurent (polynomialNorthSource n p)) =
      (sourceBlock (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF ⟨r+1,by omega⟩ / variableF ⟨r,by omega⟩)))).mulVec
        (fun p => permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)
          (evalLaurent (polynomialNorthSource n p))) := by
  simp only [polynomialNorthSource_eval_numerator, map_mul, permSpectral_const]
  change constF n (1/(2*(d:ℂ))) • northNumerator n =
    Matrix.mulVec _ (constF n (1/(2*(d:ℂ))) • _)
  rw [Matrix.mulVec_smul]
  exact congrArg (fun v => constF n (1/(2*(d:ℂ))) • v) (northNumerator_covariance r hr)

lemma polynomialNorthSource_parity {n : ℕ} (k : Fin n) (p : SourcePairing n) :
    signSpectral k (evalLaurent (polynomialNorthSource n p)) =
      occupancySign p.val k.castSucc * evalLaurent (polynomialNorthSource n p) := by
  simp only [polynomialNorthSource_eval_numerator, map_mul, signSpectral_const,
    northNumerator_parity]
  ring

lemma permSpectral_swap_involutive {n : ℕ} (i j : Fin n) :
    Function.Involutive (permSpectral (Equiv.swap i j)) := by
  have h : (permSpectral (Equiv.swap i j)).comp (permSpectral (Equiv.swap i j)) =
      RingHom.id _ := by
    apply IsFractionRing.ringHom_ext (A := SpectralRing n)
    intro f
    change permSpectral (Equiv.swap i j) (permSpectral (Equiv.swap i j) (evalLaurent f)) = evalLaurent f
    rw [permSpectral_evalLaurent, permSpectral_evalLaurent]
    have hl : (permLaurent (Equiv.swap i j)).comp (permLaurent (Equiv.swap i j)) =
        RingHom.id _ := by
      apply AddMonoidAlgebra.ringHom_ext <;> intro e
      all_goals change permLaurent _ (permLaurent _ (monomialL _ _)) = monomialL _ _
      all_goals rw [permLaurent_monomial, permLaurent_monomial]; congr 1
      all_goals ext k; simp
    exact congrArg evalLaurent (DFunLike.congr_fun hl f)
  exact fun f => DFunLike.congr_fun h f

 

def polynomialNorthGluing (n : ℕ) : Laurent n :=
  sourceGlue (K:=Laurent n) n (fun p => reflectLaurent n (polynomialNorthSource n p))
    (polynomialNorthSource n)

lemma sourceGlue_eq_sum {K : Type*} [CommRing K] (n : ℕ)
    (v w : SourcePairing n → K) :
    sourceGlue n v w = ∑ p, ∑ q,
      v p * ((if Pairing.GluesAt (Fin.last n) p.val q.val then (1:K) else 0) * w q) := by
  simp only [sourceGlue, dotProduct, Matrix.mulVec, Finset.mul_sum, sourceBlock, glueMatrix]

end
end CriticalStrip.Diagram

end OAI
