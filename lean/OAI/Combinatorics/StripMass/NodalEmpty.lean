import Mathlib
import OAI.Combinatorics.StripMass.ResidualParityCoefficients

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma scalarValue_snoc {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (z:K) : scalarValue f (Fin.snoc a z)=scalarValue f (Fin.cons z a) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact scalarValue_permute f _ (finRotate (n+1))

lemma rationalVacuum_empty (n:ℕ) : rationalVacuum n (empty n)=spectralNormalization n := by
  simp [rationalVacuum,normalizedVacuum,attachEmpty]

lemma rationalNodalPolynomial_empty (n:ℕ) :
    rationalNodalPolynomial n (empty (n+1))=
      firstScalarHom (algebraMap ℂ (SpectralField n)) spectralA
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)) := by
  let Q:=firstScalarHom (algebraMap ℂ (SpectralField n)) spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  have htop:Q.coeff n=spectralNormalization n := by
    rw [show Q.coeff n=_ from scalarPolynomial_first_top_continuation _ _ _ _ _ _,scalarPolynomial_eval_spectral]
  have hp:(rationalNodalPolynomial n (empty (n+1))).coeff n=spectralNormalization n := by
    rw [←Pairing.padTop_empty,rationalNodalPolynomial_leading,rationalVacuum_empty]
  apply Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ (deletionBeta_injective n).injOn
  · simp only [Finset.card_univ,Fintype.card_fin]
    apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
    intro k hk
    rw [Polynomial.coeff_sub]
    by_cases he:k=n
    · subst k; exact sub_eq_zero.mpr (hp.trans htop.symm)
    · have hkn:n<k := by omega
      rw [rationalNodalPolynomial_degree n _ k (by simp [hkn]),
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (scalarPolynomial_first_degree _ _ _ _ _ _) hkn),sub_self]
  · intro i _
    have hn:=rationalNodalPolynomial_at_node (empty (n+1)) i
    simp only [empty_not_occupied,ite_false,one_mul,nodalVacuum,normalizedVacuum,attachEmpty] at hn
    rw [hn,eval_firstScalarHom]
    change nodalScalar i*1=scalarValue _ (Fin.cons (deletionBeta i) spectralA)
    rw [mul_one,←scalarValue_snoc]
    rfl

lemma rationalInterpolant_empty (n:ℕ) : rationalInterpolant n (empty (n+1))=spectralNormalization (n+1) := by
  simp only [rationalInterpolant,empty_not_occupied,ite_false,one_mul,rationalNodalPolynomial_empty]
  rw [←Polynomial.eval_map,map_firstScalarHom,eval_firstScalarHom]
  change scalarValue ((liftSpectral n).comp (algebraMap ℂ (SpectralField n)))
    (Fin.cons (spectralA (Fin.last n)) (fun i =>liftSpectral n (spectralA i)))=_
  have hc:(liftSpectral n).comp (algebraMap ℂ (SpectralField n))=algebraMap ℂ (SpectralField (n+1)) := by
    ext z; exact liftSpectral_const n z
  rw [hc]
  simp only [liftSpectral_spectralA]
  rw [←scalarValue_snoc]
  have hs:Fin.snoc (fun i:Fin n =>spectralA i.castSucc) (spectralA (Fin.last n))=spectralA := by
    funext i; induction i using Fin.lastCases <;> simp
  rw [hs]
  exact scalarPolynomial_eval_spectral (n+1)


 

 


lemma stationary_eq_empty_mul_normalized {K:Type*} [Field K] {n:ℕ}
    (w:Fin n → Weights K) (hw:VacuumRegular w) (v:Pairing n → K)
    (h: (column w).mulVec v=v) : v=fun p =>v (empty n)*normalizedVacuum w p := by
  let u:=v+(1-v (empty n)) • normalizedVacuum w
  have hu:IsNormalizedStationary w u := by
    constructor
    · simp [u,normalizedVacuum,attachEmpty]
    · simp only [u,Matrix.mulVec_add,Matrix.mulVec_smul,h,(normalizedVacuum_stationary w hw).2]
  have hh:=normalizedVacuum_unique w hw u hu
  funext p
  have he:=congrFun hh p
  change v p+(1-v (empty n))*normalizedVacuum w p=normalizedVacuum w p at he
  linear_combination he

lemma interpolant_eq_vacuum_of_residual {n:ℕ} (h:∀p,rationalInterpolationResidual n p=0) :
    rationalInterpolant n=rationalVacuum (n+1) := by
  have hs:(column (spectralWeights (n+1))).mulVec (rationalInterpolant n)=rationalInterpolant n := by
    funext p
    have hh:=h p
    unfold rationalInterpolationResidual at hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left
      (Finset.prod_ne_zero_iff.mpr (fun i _ =>rowDenominator_map_ne_zero i)))
  have he:=stationary_eq_empty_mul_normalized (spectralWeights (n+1)) (spectral_regular (n+1))
    (rationalInterpolant n) hs
  simp only [rationalInterpolant_empty] at he ⊢
  exact he

lemma rationalInterpolationResidual_empty (n:ℕ) : rationalInterpolationResidual n (empty (n+1))=0 := by
  simp only [rationalInterpolationResidual,column_mulVec_empty,sub_self,mul_zero]

lemma Pairing.exists_earlier_occupied {n:ℕ} (p:Pairing (n+1)) (hp:p≠empty (n+1)) :
    ∃i:Fin n,p.Occupied i.castSucc := by
  have hn:p.val.Nonempty := by
    by_contra h
    apply hp
    apply Subtype.ext
    exact Finset.not_nonempty_iff_eq_empty.mp h
  obtain ⟨⟨a,b⟩,hab⟩:=hn
  have hlt:a<b := p.property.1 _ hab
  have ha:a.val<n := by have:=b.isLt; exact lt_of_lt_of_le hlt (by omega)
  exact ⟨⟨a.val,ha⟩,b,Or.inl hab⟩


 

 


 
structure VacuumPolynomialData (n:ℕ) where
  P : Pairing (n+1) → Polynomial (Laurent n)
  map_P : ∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p
  box_P : ∀p,PolynomialBox (P p) (fun _ =>2*n)
  eval_P : ∀p,evalLaurent (lastLaurent p (P p))=rationalVacuum (n+1) p

namespace VacuumPolynomialData
variable {n:ℕ} (D:VacuumPolynomialData n)
def W : Pairing (n+1) → Laurent (n+1) := fun p =>lastLaurent p (D.P p)
lemma degree : LastDegree n D.P :=
  LastDegree.of_map _ (IsFractionRing.injective (SpectralRing n) (SpectralField n))
    (by simpa only [D.map_P] using rationalNodalPolynomial_degree n)
lemma box (p:Pairing (n+1)) : LaurentBox (D.W p) (fun _ =>2*n) :=
  lastLaurent_box p (D.P p) (D.box_P p) (D.degree p)
include D in
lemma interpolant : ∀p,rationalInterpolant n p=rationalVacuum (n+1) p := by
  intro p
  rw [←lastLaurent_map p (D.P p) (D.map_P p)]
  exact D.eval_P p
end VacuumPolynomialData

lemma spectralNormalization_zero : spectralNormalization 0=1 := by
  rw [←scalarPolynomial_eval_spectral]
  exact scalarValue_zero _ _
lemma rationalVacuum_zero (p:Pairing 0) : rationalVacuum 0 p=1 := by
  have hp:p=empty 0 := (p.eq_empty_iff).mpr (fun i =>Fin.elim0 i)
  rw [hp,rationalVacuum_empty,spectralNormalization_zero]
lemma Pairing.one_eq_empty (p:Pairing 1) : p=empty 1 := by
  apply p.eq_empty_iff.mpr
  rintro i ⟨j,hj⟩
  have he:j=i := Subsingleton.elim _ _
  exact p.adj_irrefl i (he ▸ hj)
lemma rationalVacuum_one (p:Pairing 1) : rationalVacuum 1 p=1 := by
  rw [p.one_eq_empty,rationalVacuum_empty,←scalarPolynomial_eval_spectral]
  convert scalarValue_one (algebraMap ℂ (SpectralField 1)) (spectralA 0) using 1
  congr 2
  funext i
  congr 1
  exact Subsingleton.elim _ _

lemma rationalNodalPolynomial_zero (p:Pairing 1) : rationalNodalPolynomial 0 p=1 := by
  rw [p.one_eq_empty]
  simp [rationalNodalPolynomial,rationalVacuum_zero,Lagrange.nodal,Lagrange.interpolate]

noncomputable def vacuumData_zero : VacuumPolynomialData 0 where
  P := fun _ =>1
  map_P := fun p =>by rw [Polynomial.map_one,rationalNodalPolynomial_zero]
  box_P := fun p =>by
    convert (PolynomialBox.one (n:=0)) using 1
  eval_P := fun p =>by
    rw [rationalVacuum_one]
    simp [lastLaurent,p.one_eq_empty,evalLaurent]


 

 


 

theorem residual_saturation {n:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (bP:∀p,PolynomialBox (P p) (fun _ =>2*(n+1)))
    (hflat:∀(b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z 0=(if b then constF (n+2) phase^3 else 1) → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (hpair:∀(h2:2≤n+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin (n+1)).castSucc=constF (n+2) phase^s*z (⟨0,by omega⟩:Fin (n+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    ∀p,rationalInterpolationResidual (n+1) p=0 := by
  have hd:LastDegree (n+1) P :=
    LastDegree.of_map _ (IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)))
      (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hb:∀p,LaurentBox (laurentResidual (fun q =>lastLaurent q (P q)) p) (fun _ =>2*((n+1)+1)) := by
    intro p
    convert laurentResidual_box (fun q =>lastLaurent q (P q)) (2*(n+1))
      (fun q =>lastLaurent_box q (P q) (bP q) (hd q)) p using 1
  intro p
  by_cases hp:p=empty (n+2)
  · subst p; exact rationalInterpolationResidual_empty _
  · obtain ⟨i,hi⟩:=p.exists_earlier_occupied hp
    exact residual_zero_of_root_grid P hP hb p i hi
      (residual_root_grid_of_positive P hP i p hi (fun j b =>residual_positive_roots P hP hflat hpair i j b p))


 

 


lemma LastMatrix.lastValue_map {K L:Type*} [CommRing K] [CommRing L] {n m:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (f:K →+* L) (b s:L) (P:Pairing (n+1) → Polynomial K) :
    CriticalStrip.Diagram.lastValue f b s (matrixPolynomial M P)=(M.map f).mulVec (CriticalStrip.Diagram.lastValue f b s P) := by
  funext p
  simp only [CriticalStrip.Diagram.lastValue,matrixPolynomial,Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul,Polynomial.eval₂_C,Matrix.mulVec,dotProduct,Matrix.map_apply]
  split_ifs with hp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · simp only [hq,ite_true]; ring
    · rw [hM p q (by simp [hp,hq]),map_zero,zero_mul,mul_zero]
      simp
  · apply Finset.sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),map_zero,zero_mul,zero_mul]
    · simp [hq]

lemma pairEvaluation_lastLaurent {n:ℕ} (s:ℕ) (p:Pairing (n+3)) (P:Polynomial (Laurent (n+2))) :
    pairEvaluation (n+1) s (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+3) =>P.map (pairEvaluation n s).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (pairPoint n s) (pairPoint_ne_zero n s) p P
  simpa only [freePoint_pair,pairEvaluation,lastValue,ite_mul,one_mul] using h

lemma freePoint_delete (n:ℕ) : freePoint (deletePoint n)=deletePoint (n+1) := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [freePoint,Fin.snoc_last,deletePoint]; rfl
  | cast i => simp only [freePoint,Fin.snoc_castSucc,deletePoint,liftSpectral_variable]; rfl

lemma freePoint_merge (n:ℕ) : freePoint (mergePoint n)=mergePoint (n+1) := by
  rw [mergePoint,freePoint_cons,freePoint_delete]
  simp only [map_mul,liftSpectral_const,liftSpectral_variable,Fin.castSucc_zero]
  rfl

lemma deleteEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n)) :
    deleteEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+1) =>P.map (deleteEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (deletePoint n) (fun i =>variableF_ne_zero i.succ) p P
  simpa only [freePoint_delete,deleteEvaluation,lastValue,ite_mul,one_mul] using h

lemma mergeEvaluation_lastLaurent {n:ℕ} (p:Pairing (n+2)) (P:Polynomial (Laurent (n+1))) :
    mergeEvaluation (n+1) (lastLaurent p P)=
      lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
        (fun _ : Pairing (n+2) =>P.map (mergeEvaluation n).toRingHom) p := by
  have h:=torusEvaluation_free_lastLaurent (mergePoint n) (mergePoint_ne_zero n) p P
  simpa only [freePoint_merge,mergeEvaluation,lastValue,ite_mul,one_mul] using h

lemma functionMatrix_map_hom {K L:Type*} [CommRing K] [CommRing L] {α β:Type*}
    (f:K →+* L) (g:α → β) : (functionMatrix (K:=K) g).map f=functionMatrix (K:=L) g := by
  ext p q
  simp only [Matrix.map_apply,functionMatrix,optionMatrix]
  split_ifs <;> simp

lemma deletionMap_map {n m k:ℕ} (f:SpectralField m →+* SpectralField k) (r:ℕ) (hr:r+2≤n+2) :
    (deletionMap (m:=m) r hr).map f=deletionMap (m:=k) r hr := by
  let E₁ : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let E₀ : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  have hw:(deletionWeights:Weights (SpectralField m)).map f=deletionWeights := by simp [Weights.map,deletionWeights]
  calc
    _ = S.map f * (E₁*E₀).map f := Matrix.map_mul
    _ = S.map f * (E₁.map f*E₀.map f) :=
      congrArg (fun M => S.map f * M) (Matrix.map_mul (L := E₁) (M := E₀) (f := f))
    _ = _ := by
      dsimp only [S,E₁,E₀]
      rw [localR_map_hom,functionMatrix_map_hom,functionMatrix_map_hom,hw]
      rfl

lemma mergeMap_lift {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) :
    (mergeMap (m:=m) r hr).map (liftSpectral m)=mergeMap (m:=m+1) r hr := by
  let E : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb ⟨r+1,by omega⟩))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase))
  have hw:(mergeWeights (constF m phase)).map (liftSpectral m)=mergeWeights (constF (m+1) phase) := by
    simp [Weights.map,mergeWeights,map_div₀,liftSpectral_const]
  calc
    _ = S.map (liftSpectral m) * E.map (liftSpectral m) := Matrix.map_mul
    _ = _ := by
      dsimp only [S,E]
      rw [localR_map_hom,functionMatrix_map_hom,hw]
      rfl

lemma liftSpectral_fcos {n:ℕ} (i:Fin n) (k:ℤ) :
    liftSpectral n (fcos i k)=fcos i.castSucc k := by
  simp only [fcos_eq,torusCos]
  simp only [map_div₀,map_add,map_mul,map_pow,map_inv₀,liftSpectral_const,liftSpectral_variable,map_ofNat]

lemma deletePairPolynomial_free (n:ℕ) :
    (deletePairPolynomial n).eval₂ (liftSpectral (n+1)) (spectralA (Fin.last (n+1)))=deletePairScalar (n+1) := by
  simp only [deletePairPolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_sub,Polynomial.eval₂_X]
  unfold deletePairScalar
  simp only [map_mul,map_prod,map_add,map_sub,liftSpectral_fcos,liftSpectral_const,Fin.castSucc_zero,Fin.prod_univ_castSucc]
  have he:fcos (Fin.last (n+1)) (-3)=spectralA (Fin.last (n+1)) := by
    have h:=phaseCosine (Fin.last (n+1)) 0
    norm_num only at h
    simpa only [zpow_zero,one_mul,spectralA] using h.symm
  simp only [Fin.succ_last,he,mul_assoc]
  rfl

lemma mergePairPolynomial_free (n:ℕ) :
    (mergePairPolynomial n).eval₂ (liftSpectral (n+1)) (spectralA (Fin.last (n+1)))=mergePairScalar (n+1) := by
  simp only [mergePairPolynomial,Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_add,Polynomial.eval₂_X]
  unfold mergePairScalar
  simp only [map_mul,map_prod,map_add,liftSpectral_fcos,liftSpectral_const,Fin.castSucc_zero,Fin.prod_univ_castSucc]
  have he:fcos (Fin.last (n+1)) (-3)=spectralA (Fin.last (n+1)) := by
    have h:=phaseCosine (Fin.last (n+1)) 0
    norm_num only at h
    simpa only [zpow_zero,one_mul,spectralA] using h.symm
  simp only [Fin.succ_last,he,mul_assoc]
  rfl


 

 


lemma pairPoint_weights {n s:ℕ} (hs:s≤3) :
    (fun i =>torusWeights (constF (n+1) phase^3/pairPoint n s i))=pairEarlierWeights n s :=
  funext (fun i =>congrArg torusWeights (pairArgument hs i))

lemma rationalAt_pair_vacuum {n s:ℕ} (hs:s≤3) (p:Pairing (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (rationalVacuum (n+2) p)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n s)*
        normalizedVacuum (pairEarlierWeights n s) p) := by
  have h:=rationalAt_torusVacuum (pairPoint n s) (pairPoint_ne_zero n s)
    (pairEarlier_L hs) (by rw [pairPoint_weights hs]; exact pairEarlier_regular n s) p
  rw [pairPoint_weights hs,show (fun i =>torusCos ((pairPoint n s i)^2/constF (n+1) phase^3))=
    pairCosines n s from funext (fun i =>pairPoint_cosine i)] at h
  exact h

lemma deleteEvaluation_vacuum {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀p,evalLaurent (W p)=rationalVacuum n p) (p:Pairing n) :
    deleteEvaluation n (W p)=scalarValue (algebraMap ℂ (SpectralField (n+1)))
      (fun i:Fin n =>fcos i.succ (-3))*normalizedVacuum (deleteWeights n) p := by
  have h:=torusEvaluation_vacuum W hW (deletePoint n) (fun i =>variableF_ne_zero i.succ)
    (fun i =>torusL_phaseRow_ne_zero i.succ 3 (by omega)) (deleteWeights_regular n) p
  rw [deletePoint_cosines] at h
  exact h

lemma mergeEvaluation_vacuum {n:ℕ} (W:Pairing (n+1) → Laurent (n+1))
    (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p) (p:Pairing (n+1)) :
    mergeEvaluation n (W p)=scalarValue (algebraMap ℂ (SpectralField (n+1)))
      (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*normalizedVacuum (mergeNewWeights n) p := by
  have h:=torusEvaluation_vacuum W hW (mergePoint n) (mergePoint_ne_zero n)
    (mergePoint_L n) (by rw [mergePoint_weights]; exact mergeNewWeights_regular n) p
  rw [mergePoint_cosines,mergePoint_weights] at h
  exact h

lemma deletePairCandidate_value {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 3 (lastLaurent p (P p))=
      scalarValue (algebraMap ℂ (SpectralField (n+2))) (pairCosines (n+1) 3)*
        normalizedVacuum (pairEarlierWeights (n+1) 3) p := by
  rw [pairEvaluation_lastLaurent]
  change lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
    (fun p =>(P p).map (pairEvaluation n 3).toRingHom) p=_
  rw [rationalNodalPolynomial_pair_delete W hW Q hQ hprev P hP,lastValue_mul_poly_map,
    (deletionMap_last 0 (show 2≤n+2 by omega)).lastValue_map,deletePairPolynomial_free,deletionMap_map]
  have he:lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
      (fun q =>(Q q).map (deleteEvaluation n).toRingHom)=
      fun q =>deleteEvaluation (n+1) (lastLaurent q (Q q)) := by
    funext q
    exact (deleteEvaluation_lastLaurent q (Q q)).symm
  rw [he]
  simp_rw [deleteEvaluation_vacuum _ hprev]
  change deletePairScalar (n+1)*((deletionMap 0 (show 2≤n+3 by omega)).mulVec
    (scalarValue (algebraMap ℂ (SpectralField (n+2))) (fun i:Fin (n+1) =>fcos i.succ (-3)) • normalizedVacuum (deleteWeights (n+1))) p)=_
  rw [Matrix.mulVec_smul,scalar_pair_delete,normalizedVacuum_pair_delete]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

lemma mergePairCandidate_value {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 2 (lastLaurent p (P p))=
      scalarValue (algebraMap ℂ (SpectralField (n+2))) (pairCosines (n+1) 2)*
        normalizedVacuum (pairEarlierWeights (n+1) 2) p := by
  rw [pairEvaluation_lastLaurent]
  change lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
    (fun p =>(P p).map (pairEvaluation n 2).toRingHom) p=_
  rw [rationalNodalPolynomial_pair_merge W hW Q hQ hprev P hP,lastValue_mul_poly_map,
    (mergeMap_last 0 (show 2≤n+2 by omega)).lastValue_map,mergePairPolynomial_free,mergeMap_lift]
  have he:lastValue (liftSpectral (n+1)) (spectralA (Fin.last (n+1))) (torusSin (variableF (Fin.last (n+1))))
      (fun q =>(Q q).map (mergeEvaluation n).toRingHom)=
      fun q =>mergeEvaluation (n+1) (lastLaurent q (Q q)) := by
    funext q
    exact (mergeEvaluation_lastLaurent q (Q q)).symm
  rw [he]
  simp_rw [mergeEvaluation_vacuum _ hprev]
  change mergePairScalar (n+1)*((mergeMap 0 (show 2≤n+3 by omega)).mulVec
    (scalarValue (algebraMap ℂ (SpectralField (n+2)))
      (Fin.cons (fcos 0 (-1)) (fun i:Fin (n+1) =>fcos i.succ (-3))) • normalizedVacuum (mergeNewWeights (n+1))) p)=_
  rw [Matrix.mulVec_smul,scalar_pair_merge,normalizedVacuum_pair_merge]
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

 

theorem residual_pair_delete {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 3 (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [deletePairCandidate_value W hW Q hQ hprev P hP]
  exact rationalAt_pair_vacuum (by omega) q

theorem residual_pair_merge {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+3)) :
    pairEvaluation (n+1) 2 (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  apply residual_specialization_zero
  intro q
  rw [mergePairCandidate_value W hW Q hQ hprev P hP]
  exact rationalAt_pair_vacuum (by omega) q

 

 


lemma residual_flat_universal {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀p,evalLaurent (W p)=rationalVacuum n p)
    (D:VacuumPolynomialData n)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0)
    (h:z 0=(if b then constF (n+2) phase^3 else 1)) (p:Pairing (n+2)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  cases b
  · exact firstFlatEvaluation_zero_universal _ (residual_firstFlat D.interpolant P hP p) z hz h
  · exact firstThreeEvaluation_zero_universal _ (residual_firstThree W hW D.interpolant P hP p) z hz h

lemma vacuumData_one_exists : Nonempty (VacuumPolynomialData 1) := by
  let W:Pairing 0 → Laurent 0:=fun _ =>1
  have hW:∀p,evalLaurent (W p)=rationalVacuum 0 p := by
    intro p; rw [rationalVacuum_zero]; exact map_one _
  have bW:∀p,LaurentBox (W p) (fun _ =>2*0-2) := by
    intro p; exact LaurentBox.one
  let D:=vacuumData_zero
  choose P hP bP using rationalNodalPolynomial_laurent_box W D.W hW D.eval_P bW D.box
  have hs:∀p,rationalInterpolationResidual 1 p=0 :=
    residual_saturation P hP (by simpa using bP) (residual_flat_universal W hW D P hP)
      (by intro h2; omega)
  have he:=interpolant_eq_vacuum_of_residual hs
  exact ⟨⟨P,hP,by simpa using bP,fun p =>by rw [lastLaurent_map p (P p) (hP p)]; exact congrFun he p⟩⟩

lemma vacuumData_step_exists {n:ℕ} (D:VacuumPolynomialData n) (E:VacuumPolynomialData (n+1)) :
    Nonempty (VacuumPolynomialData (n+2)) := by
  have bD:∀p,LaurentBox (D.W p) (fun _ =>2*(n+1)-2) := by
    simpa [Nat.mul_add] using D.box
  choose P hP bP using rationalNodalPolynomial_laurent_box D.W E.W D.eval_P E.eval_P bD E.box
  have hpair : ∀(h2:2≤(n+1)+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin ((n+1)+2) → SpectralField ((n+1)+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin ((n+1)+1)).castSucc=constF ((n+1)+2) phase^s*z (⟨0,by omega⟩:Fin ((n+1)+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
    intro h2 s hs z hz hh p
    rcases hs with rfl|rfl
    · exact pairEvaluation_zero_universal 2 _
        (residual_pair_merge D.W D.eval_P E.P E.map_P E.eval_P P hP p) z hz hh
    · exact pairEvaluation_zero_universal 3 _
        (residual_pair_delete D.W D.eval_P D.P D.map_P D.eval_P P hP p) z hz hh
  have hs:∀p,rationalInterpolationResidual (n+2) p=0 :=
    residual_saturation P hP (by simpa [Nat.mul_add] using bP)
      (residual_flat_universal D.W D.eval_P E P hP) hpair
  have he:=interpolant_eq_vacuum_of_residual hs
  exact ⟨⟨P,hP,by simpa [Nat.mul_add] using bP,
    fun p =>by rw [lastLaurent_map p (P p) (hP p)]; exact congrFun he p⟩⟩

theorem vacuumData_exists : ∀n,Nonempty (VacuumPolynomialData n) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨vacuumData_zero⟩
  | one => exact vacuumData_one_exists
  | more n hn hn1 =>
    obtain ⟨D⟩:=hn
    obtain ⟨E⟩:=hn1
    exact vacuumData_step_exists D E

noncomputable def vacuumData (n:ℕ) : VacuumPolynomialData n := Classical.choice (vacuumData_exists n)

 

theorem vacuum_interpolation_stationary : ∀n p,rationalInterpolationResidual n p=0 := by
  intro n p
  have h: rationalInterpolant n=rationalVacuum (n+1) := funext (vacuumData n).interpolant
  simp only [rationalInterpolationResidual,h,rationalVacuum_stationary,sub_self,mul_zero]

end
end CriticalStrip.Diagram

end OAI
