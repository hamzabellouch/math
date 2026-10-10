import Mathlib
import OAI.Combinatorics.StripMass.NodalTorusValue

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

 

theorem rationalNodalPolynomial_pair_merge {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p) :
    (fun p =>(P p).map (pairEvaluation n 2).toRingHom)=
      fun p =>mergePairPolynomial n*
        matrixPolynomial (mergeMap 0 (show 2≤n+3 by omega))
          (fun q =>(Q q).map (mergeEvaluation n).toRingHom) p := by
  let Q':Pairing (n+2) → Polynomial (SpectralField (n+1)):=fun p =>(Q p).map (mergeEvaluation n).toRingHom
  let M:Matrix (Pairing (n+3)) (Pairing (n+2)) (SpectralField (n+1)):=mergeMap 0 (by omega)
  have hQd:LastDegree (n+1) Q':=mappedNodal_degree Q hQ _
  have hM:LastMatrix M:=mergeMap_last 0 (show 2≤n+2 by omega)
  have hMd:LastDegree (n+1) (matrixPolynomial M Q'):=hM.degree Q' hQd
  have hright:LastDegree (n+2) (fun p =>mergePairPolynomial n*matrixPolynomial M Q' p):=
    LastDegree.mul_poly _ hMd _ (mergePairPolynomial_degree n)
  apply lastPolynomial_unique _ _ (mappedNodal_degree P hP _) hright _ (pairBeta_injective n 2 (Or.inl rfl))
  · intro p
    rw [pairMapped_merge_leading P hP p]
    rw [LastDegree.mul_poly_top _ hMd _ (mergePairPolynomial_degree n) p,mergePairPolynomial_top]
    rw [hM.leading (mergeMap 0 (show 2≤n+2 by omega)) (fun p q =>mergeMap_padTop 0 (by omega) p q)]
    have he:(fun q:Pairing (n+1) =>(Q' q.padTop).coeff (n+1))=
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3))) •
          normalizedVacuum (mergeNewWeights n) := funext (mergeMapped_leading Q hQ)
    rw [he,Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro p i
    by_cases hi:i=1
    · subst i
      rw [show pairBeta n 2 1=pairEvaluation n 2 (betaL 1) from (pairEvaluation_betaL 2 1).symm,
        rationalNodalPolynomial_pair_self W hW P hP 2 (Or.inl rfl)]
      rw [pairEvaluation_betaL,Polynomial.eval_mul,mergePairPolynomial_eval]
      change 0=mergePairScalar n*(fcos 0 7+fcos 0 (-1))*_
      have hf:=fcos_sub_eight (0:Fin (n+1)) 7
      norm_num only at hf
      rw [hf]
      ring
    · have he: lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 2 i) (torusSin (deletionNode (pairIndex n i)))
          (fun p =>(P p).map (pairEvaluation n 2).toRingHom)=
          lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 2 i) (torusSin (deletionNode (pairIndex n i)))
            (fun p =>mergePairPolynomial n*matrixPolynomial M Q' p) := by
        rw [mappedNodal_pair_node (by omega) P hP i hi,lastValue_mul_poly,hM.lastValue]
        rw [pairBeta_of_ne i hi,mergeMapped_node Q hprev]
        rw [Matrix.mulVec_smul,smul_smul]
        rw [normalizedVacuum_pairNode_merge,mergePairPolynomial_eval]
        have hs:=scalar_pair_merge_snoc (n:=n) i hi
        rw [pairBeta_of_ne i hi] at hs
        rw [hs]
      have hp:=congrFun he p
      by_cases ho:p.Occupied (Fin.last (n+2))
      · simp only [lastValue,Polynomial.eval₂_id,ho,ite_true] at hp
        exact mul_left_cancel₀ (deletionNode_sine_ne_zero _) hp
      · simpa only [lastValue,Polynomial.eval₂_id,ho,ite_false] using hp


 

 


lemma torusEvaluation_fieldMap {n m k:ℕ} (f:SpectralField m →+* SpectralField k)
    (hf:∀c,f (constF m c)=constF k c)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (P:Laurent n) :
    f (torusEvaluation z hz P)=torusEvaluation (fun i =>f (z i)) (fun i =>(map_ne_zero f).mpr (hz i)) P := by
  have he:f.comp (torusEvaluation z hz).toRingHom=
      (torusEvaluation (fun i =>f (z i)) (fun i =>(map_ne_zero f).mpr (hz i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change f (torusEvaluation z hz (monomialL _ _))=torusEvaluation _ _ (monomialL _ _)
    all_goals simp only [torusEvaluation_monomial,map_mul,map_prod,map_zpow₀,hf]
  exact DFunLike.congr_fun he P

def freePoint {n m:ℕ} (z:Fin n → SpectralField m) : Fin (n+1) → SpectralField (m+1) :=
  Fin.snoc (fun i =>liftSpectral m (z i)) (variableF (Fin.last m))

lemma freePoint_ne_zero {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (i:Fin (n+1)) : freePoint z i≠0 := by
  induction i using Fin.lastCases with
  | last => simpa only [freePoint,Fin.snoc_last] using variableF_ne_zero (Fin.last m)
  | cast i => simpa only [freePoint,Fin.snoc_castSucc] using (map_ne_zero (liftSpectral m)).mpr (hz i)

lemma freePoint_variable (m:ℕ) : freePoint (@variableF m)=variableF := by
  funext i; induction i using Fin.lastCases <;> simp [freePoint]

lemma freePoint_cons {n m:ℕ} (a:SpectralField m) (z:Fin n → SpectralField m) :
    freePoint (Fin.cons a z)=Fin.cons (liftSpectral m a) (freePoint z) := by
  unfold freePoint
  have he:(fun i =>liftSpectral m ((Fin.cons a z : Fin (n+1) → SpectralField m) i))=
      Fin.cons (liftSpectral m a) (fun i =>liftSpectral m (z i)) := by
    funext i; induction i using Fin.cases <;> simp
  rw [he,←Fin.cons_snoc_eq_snoc_cons]

lemma torusEvaluation_free_lastLaurent {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    torusEvaluation (freePoint z) (freePoint_ne_zero z hz) (lastLaurent p P)=
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last m)) else 1)*
        (P.map (torusEvaluation z hz).toRingHom).eval₂ (liftSpectral m) (spectralA (Fin.last m)) := by
  dsimp only [freePoint]
  rw [torusEvaluation_lastLaurent _ (fun i =>(map_ne_zero (liftSpectral m)).mpr (hz i)) _ (variableF_ne_zero _)]
  have he:(torusEvaluation (fun i =>liftSpectral m (z i)) (fun i =>(map_ne_zero (liftSpectral m)).mpr (hz i))).toRingHom=
      (liftSpectral m).comp (torusEvaluation z hz).toRingHom := by
    apply RingHom.ext
    intro Q
    exact (torusEvaluation_fieldMap (liftSpectral m) (liftSpectral_const m) z hz Q).symm
  rw [he,Polynomial.eval_map,←Polynomial.eval₂_map]
  rfl

lemma freePoint_firstFlat (n:ℕ) : freePoint (firstFlatPoint n)=firstFlatPoint (n+1) := by
  rw [firstFlatPoint,freePoint_cons,map_one,freePoint_variable]
  rfl
lemma freePoint_firstThree (n:ℕ) : freePoint (firstThreePoint n)=firstThreePoint (n+1) := by
  rw [firstThreePoint,freePoint_cons,map_pow,liftSpectral_const,freePoint_variable]
  rfl
lemma freePoint_pair (n s:ℕ) : freePoint (pairPoint n s)=pairPoint (n+1) s := by
  unfold pairPoint
  rw [freePoint_cons,freePoint_cons]
  simp only [map_mul,map_pow,liftSpectral_const,liftSpectral_variable,Fin.castSucc_zero]
  congr 2
  funext i
  induction i using Fin.lastCases with
  | last => simp only [freePoint,Fin.snoc_last]; rfl
  | cast i => simp only [freePoint,Fin.snoc_castSucc,liftSpectral_variable]; rfl

lemma firstFlatEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    firstFlatEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (fun _ : Pairing (n+2) =>P.map (firstFlatEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (firstFlatPoint n) (firstFlatPoint_ne_zero n) p P
  simpa only [freePoint_firstFlat,firstFlatEvaluation,lastValue,ite_mul,one_mul] using h

lemma firstThreeEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    firstThreeEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (fun _ : Pairing (n+2) =>P.map (firstThreeEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (firstThreePoint n) (firstThreePoint_ne_zero n) p P
  simpa only [freePoint_firstThree,firstThreeEvaluation,lastValue,ite_mul,one_mul] using h


 

 


lemma lastValue_spectral (n:ℕ) :
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (rationalNodalPolynomial n)=rationalInterpolant n := by
  funext p; simp only [lastValue,rationalInterpolant,ite_mul,one_mul]

lemma lastValue_C_mul {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (a:K) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    lastValue f b s (fun p =>Polynomial.C a*P p)=f a • lastValue f b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_mul,Polynomial.eval₂_C,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

lemma lastValue_firstZero_spectral (n:ℕ) :
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (firstZeroPolynomial (fun i =>(spectralWeights n i).tile) (constF n d) (constF n c)
        (constF n C) (rationalNodalPolynomial n))=
      (spectralA (Fin.last n)+constF (n+1) C) •
        firstZeroRaw (fun i =>(spectralWeights (n+1) i).tile) (rationalInterpolant n) := by
  let z:SpectralField (n+1):=variableF (Fin.last n)
  have hL:torusL (constF (n+1) phase^3/z)≠0 := by
    rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  have ht:=torus_last_cleared z (variableF_ne_zero _) hL
  have h:=firstZeroPolynomial_evaluation (liftSpectral n) (fun i =>(spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C)
    (spectralA (Fin.last n)) (torusSin z) (torusSin (constF (n+1) phase^3/z))
    (fun t =>(spectralA (Fin.last n)+constF (n+1) C)*(spectralWeights (n+1) (Fin.last n)).tile t)
    (rationalNodalPolynomial n)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.2.1)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using ht.2.2.2)
    (by simpa only [liftSpectral_const,z,spectralA,spectralWeights] using torus_sine_pair z (variableF_ne_zero _))
  rw [lastValue_spectral] at h
  have he:Fin.snoc (fun i t =>liftSpectral n ((spectralWeights n i).tile t))
      (fun t =>(spectralA (Fin.last n)+constF (n+1) C)*(spectralWeights (n+1) (Fin.last n)).tile t)=
      fun i t =>(Fin.snoc (fun _ =>1) (spectralA (Fin.last n)+constF (n+1) C):Fin (n+1) → SpectralField (n+1)) i *
        (spectralWeights (n+1) i).tile t := by
    funext i t
    induction i using Fin.lastCases <;> simp only [Fin.snoc_last,Fin.snoc_castSucc,
      liftSpectral_weights_tile,one_mul]
  rw [he,firstZeroRaw_rowScale] at h
  simpa only [Fin.prod_univ_castSucc,Fin.snoc_last,Fin.snoc_castSucc,Finset.prod_const_one,one_mul] using h.symm

lemma firstFlatCandidate_value {n:ℕ}
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstFlatEvaluation (n+1) (lastLaurent p (P p))=
      (∏j:Fin (n+1),(spectralA j+constF (n+1) C))*
        firstZeroRaw (fun j =>(spectralWeights (n+1) j).tile) (rationalVacuum (n+1)) p := by
  rw [firstFlatEvaluation_lastLaurent]
  have he:=rationalNodalPolynomial_firstFlat hprev P hP
  have hv: lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstFlatEvaluation n).toRingHom) p = _ :=
    congrFun (congrArg (lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))) he) p
  change lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstFlatEvaluation n).toRingHom) p=_
  rw [hv,lastValue_C_mul,lastValue_firstZero_spectral,show rationalInterpolant n=rationalVacuum (n+1) from funext hprev]
  simp only [Pi.smul_apply,smul_eq_mul,map_prod,map_add,liftSpectral_spectralA,liftSpectral_const,
    Fin.prod_univ_castSucc]
  ring

lemma rationalVacuum_raw_stationary (n:ℕ) :
    ((rawColumn (@rowNumerator n)).map (algebraMap (SpectralRing n) (SpectralField n))).mulVec (rationalVacuum n)=
      (∏i:Fin n,evalLaurent (rowDenominator i)) • rationalVacuum n := by
  rw [rawColumn_map]
  simp_rw [rowNumerator_map]
  rw [rawColumn_scale,Matrix.smul_mulVec]
  exact congrArg (fun v =>(∏i:Fin n,evalLaurent (rowDenominator i)) • v) (rationalVacuum_stationary n)

lemma residual_specialization_zero {n m:ℕ} (φ:Laurent n →ₐ[ℂ] SpectralField m)
    (W:Pairing n → Laurent n)
    (hV:∀p,RationalAt φ.toRingHom (rationalVacuum n p) (φ (W p))) (p:Pairing n) :
    φ (laurentResidual W p)=0 := by
  have hm:=RationalAt.mulVec (φ:=φ.toRingHom)
    ((rawColumn (@rowNumerator n)).map (algebraMap (SpectralRing n) (SpectralField n)))
    ((rawColumn (@rowNumerator n)).map φ.toRingHom) (rationalVacuum n) (fun q =>φ (W q))
    (fun q r =>RationalAt.algebraMap _) hV p
  rw [rationalVacuum_raw_stationary] at hm
  have hr: RationalAt φ.toRingHom ((∏i:Fin n,evalLaurent (rowDenominator i))*rationalVacuum n p)
      ((∏i:Fin n,φ (rowDenominator i))*φ (W p)) :=
    (RationalAt.prod _ _ _ (fun i _ =>RationalAt.algebraMap _)).mul (hV p)
  have he:=hm.unique hr
  simp only [Matrix.map_apply,Matrix.mulVec,dotProduct] at he
  simp only [laurentResidual,map_sub,map_mul,map_prod,Matrix.mulVec,dotProduct,map_sum]
  exact sub_eq_zero.mpr he

 
theorem residual_firstFlat {n:ℕ}
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstFlatEvaluation (n+1) (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [firstFlatCandidate_value hprev P hP]
  exact rationalAt_firstFlat_vacuum q


 

 


lemma lastValue_mul_poly_map {K L:Type*} [CommRing K] [CommRing L] {n:ℕ}
    (f:K →+* L) (Q:Polynomial K) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    lastValue f b s (fun p =>Q*P p)=Q.eval₂ f b • lastValue f b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_mul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

lemma firstThreeCandidate_value {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstThreeEvaluation (n+1) (lastLaurent p (P p))=
      (∏j:Fin (n+1),(spectralA j+constF (n+1) C))*
        vacantBottomExtension (rationalVacuum (n+1)) p := by
  rw [firstThreeEvaluation_lastLaurent]
  change lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
      (fun p =>(P p).map (firstThreeEvaluation n).toRingHom) p=_
  rw [rationalNodalPolynomial_firstThree W hW P hP,lastValue_C_mul]
  change _ * lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) (fun p =>(Polynomial.X+Polynomial.C (constF n C))*
    vacantBottomExtension (rationalNodalPolynomial n) p) p=_
  rw [lastValue_mul_poly_map,lastValue_vacantBottomExtension,lastValue_spectral,
    show rationalInterpolant n = rationalVacuum (n+1) from funext hprev]
  simp only [Pi.smul_apply,smul_eq_mul,map_prod,map_add,liftSpectral_spectralA,liftSpectral_const,
    Fin.prod_univ_castSucc,Polynomial.eval₂_add,Polynomial.eval₂_X,Polynomial.eval₂_C]
  ring

 
theorem residual_firstThree {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (hprev:∀p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) :
    firstThreeEvaluation (n+1) (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [firstThreeCandidate_value W hW hprev P hP]
  exact rationalAt_firstThree_vacuum q

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma torusEvaluation_unit_zpow {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (u:(Laurent n)ˣ) (k:ℤ) :
    torusEvaluation z hz ((u^k:(Laurent n)ˣ):Laurent n)=(torusEvaluation z hz (u:Laurent n))^k :=
  ((torusEvaluation z hz).toMonoidHom.comp (Units.coeHom _)).map_zpow u k

lemma substitution_torusEvaluation_general {n m:ℕ} (i:Fin (n+1)) (u:(Laurent n)ˣ)
    (v:Fin (n+1) → SpectralField m) (hv:∀j,v j≠0)
    (z:Fin n → SpectralField m) (hz:∀j,z j≠0)
    (hi:v i=torusEvaluation z hz (u:Laurent n)) (hj:∀j,v (i.succAbove j)=z j)
    (f:Laurent (n+1)) :
    torusEvaluation v hv f=torusEvaluation z hz (substituteLaurent i u f) := by
  have h:(torusEvaluation v hv).toRingHom=
      (torusEvaluation z hz).toRingHom.comp (substituteLaurent i u) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation v hv (monomialL _ _)=torusEvaluation z hz (substituteLaurent i u (monomialL _ _))
    all_goals rw [torusEvaluation_monomial,substituteLaurent_monomial,map_mul,
      torusEvaluation_monomial,torusEvaluation_unit_zpow,Fin.prod_univ_succAbove _ i]
    all_goals simp only [hi,hj,Fin.removeNth]
    all_goals ring
  exact DFunLike.congr_fun h f

lemma generic_substitution_zero {n m:ℕ} (i:Fin (n+1)) (u:(Laurent n)ˣ)
    (v:Fin (n+1) → SpectralField n) (hv:∀j,v j≠0)
    (hi:v i=evalLaurent (u:Laurent n)) (hj:∀j,v (i.succAbove j)=variableF j)
    (f:Laurent (n+1)) (h:torusEvaluation v hv f=0)
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzI:z i=torusEvaluation (z ∘ i.succAbove) (fun _ =>hz _) (u:Laurent n)) :
    torusEvaluation z hz f=0 := by
  rw [substitution_torusEvaluation i u v hv hi hj] at h
  have hf:substituteLaurent i u f=0 :=
    IsFractionRing.injective (SpectralRing n) (SpectralField n) (by simpa only [evalLaurent,map_zero] using h)
  rw [substitution_torusEvaluation_general i u z hz (z ∘ i.succAbove) (fun j =>hz _) hzI (fun j =>rfl),hf,map_zero]

lemma firstFlatEvaluation_zero_universal {n m:ℕ} (f:Laurent (n+1))
    (h:firstFlatEvaluation n f=0) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (h0:z 0=1) :
    torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 0 (monomialUnit 0 1 one_ne_zero)
    (firstFlatPoint n) (firstFlatPoint_ne_zero n) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,constF] using h0
  · simp [firstFlatPoint,monomialUnit,evalLaurent]
  · intro j; simp [firstFlatPoint]

lemma firstThreeEvaluation_zero_universal {n m:ℕ} (f:Laurent (n+1))
    (h:firstThreeEvaluation n f=0) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (h0:z 0=constF m phase^3) : torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 0 (monomialUnit 0 (phase^3) (pow_ne_zero _ phase_ne_zero))
    (firstThreePoint n) (firstThreePoint_ne_zero n) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,constF] using h0
  · simp [firstThreePoint,monomialUnit,evalLaurent_monomial_product,constF]
  · intro j; simp [firstThreePoint]

lemma pairEvaluation_zero_universal {n m:ℕ} (s:ℕ) (f:Laurent (n+2))
    (h:pairEvaluation n s f=0) (z:Fin (n+2) → SpectralField m) (hz:∀j,z j≠0)
    (h01:z 1=constF m phase^s*z 0) : torusEvaluation z hz f=0 := by
  apply generic_substitution_zero 1 (monomialUnit (variableExponent 0) (phase^s) (pow_ne_zero _ phase_ne_zero))
    (pairPoint n s) (pairPoint_ne_zero n s) _ _ f h z hz
  · simpa [monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF] using h01
  · simp only [pairPoint,monomialUnit,evalLaurent_monomial_product]
    simp [variableExponent,Pi.single_apply,constF]
  · intro j
    induction j using Fin.cases with
    | zero => simp [pairPoint]
    | succ j => simp [pairPoint]

end

 

 

noncomputable section
open scoped Classical

 

theorem residual_flat_transport {n m:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (c:SpectralField m)
    (hbase:∀(z:Fin (n+2) → SpectralField m) (hz:∀k,z k≠0),z 0=c → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i:Fin (n+1)) (z:Fin (n+2) → SpectralField m) (hz:∀k,z k≠0)
    (hi:z i.castSucc=c)
    (hL:∀j:Fin (n+1),j < i → torusL (z i.castSucc/z j.castSucc)≠0) (p:Pairing (n+2)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  induction i using Fin.induction generalizing z p with
  | zero => exact hbase z hz hi p
  | @succ i ih =>
    let σ:=Equiv.swap i.castSucc i.succ
    let z':=z ∘ topPerm σ
    have hz':∀k,z' k≠0 := fun k =>hz _
    have he (k:Fin (n+1)): z' k.castSucc=z (σ k).castSucc := by simp only [z',Function.comp_apply,topPerm_cast]
    have hs:σ i.castSucc=i.succ := Equiv.swap_apply_left _ _
    have hr:i.val+2≤n+1 := by omega
    have hzero:∀q,torusEvaluation z' hz' (laurentResidual (fun q =>lastLaurent q (P q)) q)=0 := by
      intro q
      apply ih z' hz'
      · rw [he,hs]; exact hi
      · intro j hj
        rw [he,hs,he]
        have hja:j≠i.castSucc := Fin.ne_of_lt hj
        have hjb:j≠i.succ := by apply Fin.ne_of_lt; exact hj.trans (Fin.castSucc_lt_succ)
        rw [show σ j=j from Equiv.swap_apply_of_ne_of_ne hja hjb]
        exact hL j (hj.trans (Fin.castSucc_lt_succ))
    exact residual_zero_transport P hP i.val hr z hz
      (hL i.castSucc (Fin.castSucc_lt_succ)) hzero p


 

 


def PairExchangeRegular {n m:ℕ} (z:Fin (n+1) → SpectralField m) (i j:Fin n) : Prop :=
  ∀a b:Fin n,a≠b → ¬(a=i ∧ b=j ∨ a=j ∧ b=i) →
    torusL (z b.castSucc/z a.castSucc)≠0

lemma PairExchangeRegular.perm {n m:ℕ} {z:Fin (n+1) → SpectralField m} {i j:Fin n}
    (h:PairExchangeRegular z i j) (σ:Equiv.Perm (Fin n)) :
    PairExchangeRegular (z ∘ topPerm σ) (σ.symm i) (σ.symm j) := by
  intro a b hab hij
  simp only [Function.comp_apply,topPerm_cast]
  apply h (σ a) (σ b) (fun e =>hab (σ.injective e))
  simpa only [←Equiv.eq_symm_apply] using hij

 

theorem residual_pair_transport {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (c:SpectralField m) (h2:2≤n)
    (hbase:∀(z:Fin (n+1) → SpectralField m) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin n).castSucc=c*z (⟨0,by omega⟩:Fin n).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i j:Fin n) (hij:i<j) (z:Fin (n+1) → SpectralField m) (hz:∀k,z k≠0)
    (he:z j.castSucc=c*z i.castSucc) (hL:PairExchangeRegular z i j) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  generalize hsum:i.val+j.val=t
  induction t using Nat.strong_induction_on generalizing i j z p with
  | h t ih =>
    by_cases hi:i.val=0
    · by_cases hj:j.val=1
      · apply hbase z hz
        have hi0:i=(⟨0,by omega⟩:Fin n) := Fin.ext hi
        have hj1:j=(⟨1,by omega⟩:Fin n) := Fin.ext hj
        simpa only [hi0,hj1] using he
      · let r:=j.val-1
        have hr:r+2≤n := by dsimp [r]; omega
        let a:Fin n:=⟨r,by omega⟩
        let b:Fin n:=⟨r+1,by omega⟩
        let σ:=Equiv.swap a b
        have hb:b=j := by apply Fin.ext; dsimp [b,r]; omega
        have hia:i≠a := by intro h; have:=congrArg Fin.val h; dsimp [a,r] at this; omega
        have hib:i≠b := by rw [hb]; exact Fin.ne_of_lt hij
        have hsi:σ i=i := Equiv.swap_apply_of_ne_of_ne hia hib
        have hsj:σ a=j := by rw [←hb]; exact Equiv.swap_apply_left _ _
        have horder:i<a := by change i.val<a.val; dsimp [a,r]; omega
        have hreg:torusL (z b.castSucc/z a.castSucc)≠0 := by
          apply hL a b (by rw [hb]; exact Fin.ne_of_lt (by change a.val<j.val; dsimp [a,r]; omega))
          intro h; rcases h with h|h
          · exact hia h.1.symm
          · exact hib h.2.symm
        apply residual_zero_transport P hP r hr z hz hreg
        intro q
        apply ih (i.val+a.val) (by dsimp [a,r]; omega) i a horder
          (z ∘ topPerm σ) (fun k =>hz _) _ _ q rfl
        · simpa only [Function.comp_apply,topPerm_cast,hsi,hsj] using he
        · have hh:=hL.perm σ
          have hsym:σ.symm=σ := Equiv.symm_swap _ _
          rw [hsym,hsi,show σ j=a by rw [←hb]; exact Equiv.swap_apply_right _ _] at hh
          exact hh
    · let r:=i.val-1
      have hr:r+2≤n := by dsimp [r]; omega
      let a:Fin n:=⟨r,by omega⟩
      let b:Fin n:=⟨r+1,by omega⟩
      let σ:=Equiv.swap a b
      have hb:b=i := by apply Fin.ext; dsimp [b,r]; omega
      have hja:j≠a := by intro h; have:=congrArg Fin.val h; dsimp [a,r] at this; have:=hij; change i.val<j.val at this; omega
      have hjb:j≠b := by rw [hb]; exact Ne.symm (Fin.ne_of_lt hij)
      have hsj:σ j=j := Equiv.swap_apply_of_ne_of_ne hja hjb
      have hsi:σ a=i := by rw [←hb]; exact Equiv.swap_apply_left _ _
      have horder:a<j := by change a.val<j.val; dsimp [a,r]; have:=hij; change i.val<j.val at this; omega
      have hreg:torusL (z b.castSucc/z a.castSucc)≠0 := by
        apply hL a b (by rw [hb]; exact Fin.ne_of_lt (by change a.val < i.val; dsimp [a,r]; omega))
        intro h; rcases h with h|h
        · exact hjb h.2.symm
        · exact hja h.1.symm
      apply residual_zero_transport P hP r hr z hz hreg
      intro q
      apply ih (a.val+j.val) (by dsimp [a,r]; omega) a j horder
        (z ∘ topPerm σ) (fun k =>hz _) _ _ q rfl
      · simpa only [Function.comp_apply,topPerm_cast,hsi,hsj] using he
      · have hh:=hL.perm σ
        have hsym:σ.symm=σ := Equiv.symm_swap _ _
        rw [hsym,hsj,show σ i=a by rw [←hb]; exact Equiv.swap_apply_right _ _] at hh
        exact hh

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

 

def fullPeel {n:ℕ} (i:Fin (n+1)) : Laurent (n+1) →+* LaurentPolynomial (SpectralField (n+1)) :=
  (AddMonoidAlgebra.mapRingHom ℤ (insertSpectral i)).comp (peelLaurent i)

lemma fullPeel_injective {n:ℕ} (i:Fin (n+1)) : Function.Injective (fullPeel i) :=
  (AddMonoidAlgebra.map_injective _ (insertSpectral i).injective).comp (peelLaurent_injective i)

lemma fullPeel_coeff {n:ℕ} (i:Fin (n+1)) (f:Laurent (n+1)) (k:ℤ) :
    (fullPeel i f).coeff k=insertSpectral i ((peelLaurent i f).coeff k) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

lemma LaurentBox.fullPeel {n:ℕ} {f:Laurent (n+1)} {b:Fin (n+1) → ℕ}
    (hb:LaurentBox f b) (i:Fin (n+1)) : LaurentInterval (fullPeel i f) (-(b i:ℤ)) (b i) := by
  intro k hk
  apply hb.peel i k
  intro hz
  rw [fullPeel_coeff,hz,map_zero] at hk
  exact hk rfl

lemma fullPeel_monomial {n:ℕ} (i:Fin (n+1)) (e:Fin (n+1) → ℤ) (c:ℂ) :
    fullPeel i (monomialL e c)=AddMonoidAlgebra.single (e i)
      (evalLaurent (monomialL (Function.update e i 0) c)) := by
  change AddMonoidAlgebra.mapRingHom ℤ (insertSpectral i) (peelLaurent i (monomialL e c))=_
  rw [peelLaurent_monomial,AddMonoidAlgebra.mapRingHom_single,insertSpectral_evalLaurent,insertLaurent_monomial]
  congr 3
  simp [Fin.insertNth_removeNth]

lemma evalLaurent_monomial_full {n:ℕ} (e:Fin n → ℤ) (c:ℂ) :
    evalLaurent (monomialL e c)=constF n c*∏j:Fin n,variableF j^(e j) := by
  exact (evalLaurent_monomial_product e c)

lemma fullPeel_eval {n:ℕ} (i:Fin (n+1)) (z:SpectralField (n+1)) (hz:z≠0) (f:Laurent (n+1)) :
    LaurentPolynomial.eval₂ (RingHom.id _) (Units.mk0 z hz) (fullPeel i f)=
      torusEvaluation (Function.update variableF i z)
        (fun j =>by by_cases h:j=i <;> simp [h,hz,variableF_ne_zero]) f := by
  let ψ:=torusEvaluation (Function.update variableF i z)
        (fun j =>by by_cases h:j=i <;> simp [h,hz,variableF_ne_zero])
  have he:(LaurentPolynomial.eval₂ (RingHom.id _) (Units.mk0 z hz)).comp (fullPeel i)=ψ.toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change LaurentPolynomial.eval₂ _ _ (fullPeel i (monomialL _ _))=ψ (monomialL _ _)
    all_goals rw [fullPeel_monomial, LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
    all_goals simp only [RingHom.id_apply,Units.val_zpow_eq_zpow_val,Units.val_mk0]
    all_goals rw [evalLaurent_monomial_full,torusEvaluation_monomial]
    all_goals rw [Fin.prod_univ_succAbove _ i,Fin.prod_univ_succAbove _ i]
    all_goals simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne _ _),zpow_zero,one_mul]
    all_goals ring
  exact DFunLike.congr_fun he f

end
end CriticalStrip.Diagram

end OAI
