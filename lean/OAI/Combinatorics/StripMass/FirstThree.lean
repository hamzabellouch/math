import Mathlib
import OAI.Combinatorics.StripMass.ResidualEvaluation

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma vacantBottomExtension_smul {K:Type*} [CommRing K] {n:ℕ}
    (a:K) (v:Pairing n → K) :
    vacantBottomExtension (a • v)=a • vacantBottomExtension v := by
  funext p
  by_cases hp:p.Occupied 0 <;> simp [vacantBottomExtension,hp,Pi.smul_apply]

lemma normalizedVacuum_firstThree {K:Type*} [Field K] {n:ℕ}
    (w:Fin n → Weights K) (hw:VacuumRegular w) :
    normalizedVacuum (Fin.cons identityWeights w)=vacantBottomExtension (normalizedVacuum w) := by
  have hr:VacuumRegular (Fin.cons identityWeights w) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact hw
  symm
  apply normalizedVacuum_unique _ hr
  constructor
  · rw [←Pairing.padBottom_empty,vacantBottomExtension_padBottom]
    exact (normalizedVacuum_stationary w hw).1
  · funext p
    rw [mulVec_vacantBottomExtension]
    by_cases hp:p.Occupied 0
    · simp only [vacantBottomExtension,hp,ite_true]
      apply Finset.sum_eq_zero
      intro q _
      rw [column_identity_bottom_row _ rfl _ _ hp,zero_mul]
    · rw [←p.padBottom_restrict hp,vacantBottomExtension_padBottom]
      simp only [column_padBottom,Fin.cons_succ]
      exact congrFun (normalizedVacuum_stationary w hw).2 _

def firstThreePoint (n:ℕ) : Fin (n+1) → SpectralField n :=
  Fin.cons (constF n phase^3) variableF

lemma firstThreePoint_ne_zero (n:ℕ) (i:Fin (n+1)) : firstThreePoint n i≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact variableF_ne_zero i

def firstThreeEvaluation (n:ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField n :=
  torusEvaluation (firstThreePoint n) (firstThreePoint_ne_zero n)

lemma rationalAt_firstThree_variable {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (variableF i) (firstThreePoint n i) :=
  rationalAt_variable _ _ i

lemma rationalAt_firstThree_spectralA {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (spectralA i)
      ((Fin.cons (constF n c) spectralA : Fin (n+1) → SpectralField n) i) := by
  have h:=rationalAt_torusCos (firstThreeEvaluation n)
    (((rationalAt_firstThree_variable i).pow 2).div
      ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstThreePoint_ne_zero n i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he:(constF n phase^3)^2/constF n phase^3=constF n phase^3 := by
        field_simp
      simpa only [firstThreePoint,Fin.cons_zero,he,torusCos_phase_pow,Nat.cast_ofNat,spectralA,c] using h
  | succ i => exact h

lemma rationalAt_firstThree_deletionNode {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (deletionNode i)
      ((Fin.cons (constF n phase^6) deletionNode : Fin (n+1) → SpectralField n) i) := by
  have h:=(rationalAt_firstThree_variable i).mul
    ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
  induction i using Fin.cases with
  | zero => simpa only [firstThreePoint,Fin.cons_zero,←pow_add,Nat.reduceAdd,deletionNode] using h
  | succ i => exact h

lemma firstThreeNode_ne_zero {n:ℕ} (i:Fin (n+1)) :
    ((Fin.cons (constF n phase^6) deletionNode : Fin (n+1) → SpectralField n) i)≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma torusCos_phase_nine (n:ℕ) :torusCos (constF n phase^9)= -constF n C := by
  rw [torusCos_phase_pow]
  have h:9*lambda=lambda+Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,h,Real.cos_add_pi,Complex.ofReal_neg,constF,map_neg,C]

lemma rationalAt_firstThree_deletionBeta {n:ℕ} (i:Fin (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (deletionBeta i)
      ((Fin.cons (-constF n C) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  have h:=rationalAt_torusCos (firstThreeEvaluation n)
    (((rationalAt_firstThree_deletionNode i).pow 2).div
      ((rationalAt_const (firstThreeEvaluation n) phase).pow 3)
      (pow_ne_zero _ (constF_phase_ne_zero n)))
    (div_ne_zero (pow_ne_zero _ (firstThreeNode_ne_zero i))
      (pow_ne_zero _ (constF_phase_ne_zero n)))
  induction i using Fin.cases with
  | zero =>
      have he:(constF n phase^6)^2/constF n phase^3=constF n phase^9 := by
        field_simp
      simpa only [Fin.cons_zero,he,torusCos_phase_nine,deletionBeta] using h
  | succ i => exact h

lemma rationalAt_firstThree_weights {n:ℕ} (i:Fin (n+1)) (t:Tile) :
    RationalAt (firstThreeEvaluation n).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.cons identityWeights (spectralWeights n) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  have hz:=rationalAt_firstThree_variable i
  have hq:=(rationalAt_const (firstThreeEvaluation n) phase).pow 3
  induction i using Fin.cases with
  | zero =>
      simp only [firstThreePoint,Fin.cons_zero] at hz
      have h:=hq.div hz (pow_ne_zero _ (constF_phase_ne_zero n))
      rw [div_self (pow_ne_zero _ (constF_phase_ne_zero n))] at h
      simpa only [Fin.cons_zero,torusWeights_one,spectralWeights] using
        rationalAt_torusWeights (firstThreeEvaluation n) h one_ne_zero (torusL_one_ne_zero n) t
  | succ i =>
      simp only [firstThreePoint,Fin.cons_succ] at hz
      exact rationalAt_torusWeights (firstThreeEvaluation n)
        (hq.div hz (variableF_ne_zero i))
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))
        (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero i) t

lemma rationalAt_firstThree_normalization (n:ℕ) :
    RationalAt (firstThreeEvaluation n).toRingHom (spectralNormalization (n+1))
      ((∏ j:Fin n,(spectralA j+constF n C))*spectralNormalization n) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA (Fin.cons (constF n c) spectralA)
    (rationalAt_const (firstThreeEvaluation n)) rationalAt_firstThree_spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  simp only [constF] at h
  rw [scalarPolynomial_eval_spectral,source_scalarPolynomial_flat,scalarPolynomial_eval_spectral] at h
  exact h

lemma rationalAt_firstThree_vacuum {n:ℕ} (p:Pairing (n+1)) :
    RationalAt (firstThreeEvaluation n).toRingHom (rationalVacuum (n+1) p)
      ((∏ j:Fin n,(spectralA j+constF n C))*vacantBottomExtension (rationalVacuum n) p) := by
  have hr:VacuumRegular (Fin.cons identityWeights (spectralWeights n)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact spectral_regular n
  have h:=rationalAt_normalizedVacuum _ _ rationalAt_firstThree_weights hr p
  rw [normalizedVacuum_firstThree _ (spectral_regular n)] at h
  have he:=(rationalAt_firstThree_normalization n).mul h
  have hs:rationalVacuum n=spectralNormalization n • normalizedVacuum (spectralWeights n) := rfl
  rw [hs,vacantBottomExtension_smul]
  simpa only [rationalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he


 

 


lemma firstThreeHead_zero {n:ℕ} (occupied:Prop) [Decidable occupied] :
    firstThreeEvaluation n (nodalHeadL (0:Fin (n+1)) occupied)=0 := by
  have h:RationalAt (firstThreeEvaluation n).toRingHom
      (reducedNodalHead (0:Fin (n+1)) occupied) 0 := by
    by_cases ho:occupied
    · simp only [reducedNodalHead,ite_eq_left ho]
      have hv:=(rationalAt_const (firstThreeEvaluation n) phase).pow 3 |>.div
        (rationalAt_firstThree_variable (0:Fin (n+1))) (pow_ne_zero _ (constF_phase_ne_zero n))
      simp only [firstThreePoint,Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n))] at hv
      have ht:=rationalAt_torusSin (firstThreeEvaluation n) hv one_ne_zero
      simp only [torusSin,inv_one,sub_self,zero_div] at ht
      have hh:= ((RationalAt.natCast 4).mul (rationalAt_const (firstThreeEvaluation n) (c:ℂ))).mul ht
      simpa only [mul_zero,torusSin,Nat.cast_ofNat] using hh
    · simp only [reducedNodalHead,ite_eq_right ho]
      have hh:=((rationalAt_firstThree_spectralA (0:Fin (n+1))).add
        (rationalAt_firstThree_deletionBeta (0:Fin (n+1)))).add
        (rationalAt_const (firstThreeEvaluation n) (rho:ℂ))
      simp only [Fin.cons_zero] at hh
      have he:constF n c+-constF n C+constF n rho=0 := by
        have hc:=congrArg (fun x:ℝ => constF n (x:ℂ)) c_add_rho_eq_C
        simp only [Complex.ofReal_add,constF,map_add] at hc ⊢
        linear_combination hc
      rw [he] at hh
      exact hh
  have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
    (F:=SpectralField (n+1)) (nodalHeadL (0:Fin (n+1)) occupied)
  change RationalAt _ (evalLaurent _) _ at ha
  rw [nodalHeadL_map] at ha
  exact ha.unique h

lemma nodalDatumL_firstThree_zero {n:ℕ} (W:Pairing n → Laurent n) (p:Pairing (n+2)) :
    firstThreeEvaluation n (nodalDatumL W 0 p)=0 := by
  simp only [nodalDatumL,map_mul,firstThreeHead_zero,mul_zero,zero_mul]

lemma rationalNodalPolynomial_firstThree_self {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) (p:Pairing (n+2)) :
    ((P p).map (firstThreeEvaluation n).toRingHom).eval (-constF n C)=0 := by
  have he:(P p).eval (betaL 0)=nodalDatumL W 0 p := by
    apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
    change evalLaurent ((P p).eval (betaL 0))=evalLaurent (nodalDatumL W 0 p)
    rw [nodalDatumL_map W hW]
    have hh:=rationalNodalPolynomial_at_node p (0:Fin (n+1))
    rw [eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero 0; exact one_ne_zero)]
    rw [mul_comm]
    rw [←hP] at hh
    have hf:evalLaurent ((P p).eval (betaL 0))=
        ((P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).eval (deletionBeta 0) := by
      rw [←betaL_map]
      exact (Polynomial.eval_map_apply ..).symm
    rw [hf]
    exact hh
  have hb:firstThreeEvaluation n (betaL (0:Fin (n+1)))= -constF n C := by
    have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) (betaL (0:Fin (n+1)))
    change RationalAt _ (evalLaurent _) _ at ha
    rw [betaL_map] at ha
    exact ha.unique (rationalAt_firstThree_deletionBeta 0)
  have hh:=congrArg (firstThreeEvaluation n) he
  rw [nodalDatumL_firstThree_zero] at hh
  rw [←hb]
  change ((P p).map (firstThreeEvaluation n).toRingHom).eval
    ((firstThreeEvaluation n).toRingHom (betaL 0))=0
  rw [Polynomial.eval_map_apply]
  exact hh

lemma rationalAt_firstThree_nodalWeights {n:ℕ} (i:Fin n)
    (j:Fin (n+2)) (t:Tile) :
    RationalAt (firstThreeEvaluation n).toRingHom ((nodalWeights i.succ j).tile t)
      (((Fin.cons identityWeights (nodalWeights i) : Fin (n+2) → Weights (SpectralField n)) j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
      have h:=rationalAt_firstThree_weights j t
      induction j using Fin.cases with
      | zero =>
          change RationalAt (firstThreeEvaluation n).toRingHom ((spectralWeights (n+1) 0).tile t) (identityWeights.tile t)
          exact h
      | succ j =>
          simp only [nodalWeights,Fin.snoc_castSucc]
          rw [←Fin.succ_castSucc,Fin.cons_succ,Fin.snoc_castSucc]
          exact h
  | last =>
      simp only [Fin.cons_last,nodalWeights_last]
      have hv := (rationalAt_firstThree_variable i.succ).inv (variableF_ne_zero i)
      simp only [firstThreePoint,Fin.cons_succ] at hv
      exact rationalAt_torusWeights (firstThreeEvaluation n) hv
        (inv_ne_zero (variableF_ne_zero i))
        (by rw [←inverseRowDenominator_map]; exact inverseRowDenominator_map_ne_zero i) t

lemma rationalAt_firstThree_nodalScalar {n:ℕ} (i:Fin n) :
    RationalAt (firstThreeEvaluation n).toRingHom (nodalScalar i.succ)
      ((∏ j:Fin n,(spectralA j+constF n C))*(deletionBeta i+constF n C)*nodalScalar i) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n))
    (Fin.snoc spectralA (deletionBeta i.succ))
    (Fin.snoc (Fin.cons (constF n c) spectralA) (deletionBeta i))
    (rationalAt_const (firstThreeEvaluation n))
    (fun j => by
      induction j using Fin.lastCases with
      | last => simpa using rationalAt_firstThree_deletionBeta i.succ
      | cast j => simpa using rationalAt_firstThree_spectralA j)
    (scalarPolynomial (n+2) d rho (by exact_mod_cast d_ne_zero))
  rw [←Fin.cons_snoc_eq_snoc_cons] at h
  simp only [constF] at h
  rw [source_scalarPolynomial_flat (algebraMap ℂ (SpectralField n)) (n+1)] at h
  rw [Fin.prod_univ_castSucc] at h
  simpa only [nodalScalar,Fin.snoc_castSucc,Fin.snoc_last,constF] using h

lemma rationalAt_firstThree_nodalVacuum {n:ℕ} (i:Fin n) (p:Pairing (n+2)) :
    RationalAt (firstThreeEvaluation n).toRingHom (nodalVacuum i.succ p)
      ((∏ j:Fin n,(spectralA j+constF n C))*(deletionBeta i+constF n C)*
        vacantBottomExtension (nodalVacuum i) p) := by
  have hr:VacuumRegular (Fin.cons identityWeights (nodalWeights i)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inl rfl)]
    exact nodal_regular i
  have h:=rationalAt_normalizedVacuum _ _ (rationalAt_firstThree_nodalWeights i) hr p
  rw [normalizedVacuum_firstThree _ (nodal_regular i)] at h
  have he:=(rationalAt_firstThree_nodalScalar i).mul h
  have hs:nodalVacuum i=nodalScalar i • normalizedVacuum (nodalWeights i) := rfl
  rw [hs,vacantBottomExtension_smul]
  simpa only [nodalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he


 

 


def firstThreePolynomial {K:Type*} [CommRing K] {n:ℕ} (C:K)
    (P:Pairing n → Polynomial K) : Pairing (n+1) → Polynomial K :=
  fun p => (Polynomial.X+Polynomial.C C)*vacantBottomExtension P p

lemma firstThreePolynomial_padBottom {K:Type*} [CommRing K] {n:ℕ} (C:K)
    (P:Pairing n → Polynomial K) (p:Pairing n) :
    firstThreePolynomial C P p.padBottom=(Polynomial.X+Polynomial.C C)*P p := by
  rw [firstThreePolynomial,vacantBottomExtension_padBottom]

lemma firstThreePolynomial_degree {K:Type*} [CommRing K] {n m:ℕ} (C:K)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P) :
    LastDegree (m+1) (firstThreePolynomial C P) := by
  intro p k hk
  by_cases hp:p.Occupied 0
  · simp [firstThreePolynomial,vacantBottomExtension,hp]
  · rw [←p.padBottom_restrict hp] at hk ⊢
    rw [firstThreePolynomial_padBottom]
    let q:=p.restrict (Fin.succOrderEmb (n+1))
    have ho:(q.padBottom.Occupied (Fin.last (n+1))) ↔ q.Occupied (Fin.last n) := by
      exact q.padBottom_occupied_succ (Fin.last n)
    change (if q.padBottom.Occupied (Fin.last (n+1)) then m+1≤k else m+1<k) at hk
    rw [ho] at hk
    obtain ⟨j,rfl⟩:∃j,k=j+1 := by split_ifs at hk <;> exact ⟨k-1,by omega⟩
    have hh:(P q).coeff j=0 := hP q j (by split_ifs at hk ⊢ <;> omega)
    have hh':(P q).coeff (j+1)=0 := hP q (j+1) (by split_ifs at hk ⊢ <;> omega)
    simp [add_mul,Polynomial.coeff_X_mul,hh,hh',q]

lemma firstThreePolynomial_leading {K:Type*} [CommRing K] {n m:ℕ} (C:K)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P) (p:Pairing (n+1)) :
    (firstThreePolynomial C P p.padTop).coeff (m+1)=
      vacantBottomExtension (fun q => (P q.padTop).coeff m) p := by
  by_cases hp:p.Occupied 0
  · have ht:p.padTop.Occupied 0 := by
      exact (p.padTop_occupied_castSucc 0).mpr hp
    simp [firstThreePolynomial,vacantBottomExtension,hp,ht]
  · rw [←p.padBottom_restrict hp,Pairing.padBottom_padTop,
      firstThreePolynomial_padBottom,vacantBottomExtension_padBottom]
    have hz:=hP (p.restrict (Fin.succOrderEmb n)).padTop (m+1) (by simp)
    simp [add_mul,Polynomial.coeff_X_mul,hz]

lemma firstThreeBeta_injective (n:ℕ) :
    Function.Injective (Fin.cons (-constF n C) deletionBeta : Fin (n+1) → SpectralField n) := by
  apply Fin.cons_injective_iff.mpr
  constructor
  · rintro ⟨i,he⟩
    exact deletionBeta_ne_const i (-C) (by simpa only [Complex.ofReal_neg,constF,map_neg] using he)
  · exact deletionBeta_injective n

 

theorem rationalNodalPolynomial_firstThree {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) :
    (fun p => (P p).map (firstThreeEvaluation n).toRingHom)=
      fun p => Polynomial.C (∏j:Fin n,(spectralA j+constF n C))*
        firstThreePolynomial (constF n C) (rationalNodalPolynomial n) p := by
  have hdeg:LastDegree (n+1) P :=
    LastDegree.of_map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      (IsFractionRing.injective _ _) (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hright:LastDegree (n+1) (fun p => Polynomial.C (∏j:Fin n,(spectralA j+constF n C))*
        firstThreePolynomial (constF n C) (rationalNodalPolynomial n) p) := by
    intro p k hk
    rw [Polynomial.coeff_C_mul,
      firstThreePolynomial_degree _ _ (rationalNodalPolynomial_degree n) p k hk,mul_zero]
  apply lastPolynomial_unique _ _ (hdeg.map _) hright _ (firstThreeBeta_injective n)
  · intro p
    rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,
      firstThreePolynomial_leading _ _ (rationalNodalPolynomial_degree n)]
    have hh:(fun q:Pairing n => (rationalNodalPolynomial n q.padTop).coeff n)=rationalVacuum n := by
      funext q; exact rationalNodalPolynomial_leading q
    rw [hh]
    have ha:=RationalAt.algebraMap (φ:=(firstThreeEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) ((P p.padTop).coeff (n+1))
    have hb:=congrArg (fun Q:Polynomial (SpectralField (n+1)) => Q.coeff (n+1)) (hP p.padTop)
    rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at hb
    rw [hb] at ha
    exact ha.unique (rationalAt_firstThree_vacuum p)
  · intro p i
    induction i using Fin.cases with
    | zero =>
        simp only [Fin.cons_zero]
        rw [rationalNodalPolynomial_firstThree_self W hW P hP p]
        simp [firstThreePolynomial,Polynomial.eval_mul,Polynomial.eval_add]
    | succ i =>
        simp only [Fin.cons_succ]
        have hs:=rationalAt_torusSin (firstThreeEvaluation n)
          (rationalAt_firstThree_deletionNode i.succ)
          (firstThreeNode_ne_zero i.succ)
        have he:RationalAt (firstThreeEvaluation n).toRingHom
            ((rationalNodalPolynomial (n+1) p).eval (deletionBeta i.succ))
            (((P p).map (firstThreeEvaluation n).toRingHom).eval (deletionBeta i)) := by
          rw [←hP]
          exact RationalAt.eval_map _ (rationalAt_firstThree_deletionBeta i.succ) _
        have hsin:RationalAt (firstThreeEvaluation n).toRingHom
            (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i.succ) else 1)
            (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := by
          split_ifs
          · exact hs
          · exact RationalAt.one
        have hb:=hsin.mul he
        rw [rationalNodalPolynomial_at_node] at hb
        have hv:=hb.unique (rationalAt_firstThree_nodalVacuum i p)
        apply mul_left_cancel₀ (show (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)≠0 by
          split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)
        rw [hv,Polynomial.eval_mul,Polynomial.eval_C]
        by_cases hp:p.Occupied 0
        · simp [firstThreePolynomial,vacantBottomExtension,hp]
        · rw [←p.padBottom_restrict hp,firstThreePolynomial_padBottom,vacantBottomExtension_padBottom]
          rw [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C]
          rw [show (p.restrict (Fin.succOrderEmb (n+1))).padBottom.Occupied (Fin.last (n+1)) ↔
              (p.restrict (Fin.succOrderEmb (n+1))).Occupied (Fin.last n) by
                exact Pairing.padBottom_occupied_succ _ (Fin.last n)]
          rw [←rationalNodalPolynomial_at_node]
          ring


 

 


lemma vacuumRegular_of_rationalAt {R F K:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] (φ:R →+* K) {n:ℕ}
    (w:Fin n → Weights F) (v:Fin n → Weights K)
    (h:∀i t,RationalAt φ ((w i).tile t) ((v i).tile t))
    (hv:VacuumRegular v) : VacuumRegular w := by
  have hb:∀i j,RationalAt φ ((1-restrictedColumn w) i j) ((1-restrictedColumn v) i j) := by
    intro i j
    exact (RationalAt.matrixOne i j).sub (rationalAt_column w v h i.val j.val)
  exact (RationalAt.det (1-restrictedColumn w) (1-restrictedColumn v) hb).ne_zero hv

lemma torusRegular_of_rationalAt {m n r:ℕ} (φ:Laurent m →ₐ[ℂ] SpectralField n)
    (x:Fin r → SpectralField m) (y:Fin r → SpectralField n)
    (h:∀i,RationalAt φ.toRingHom (x i) (y i))
    (hy:∀i,y i≠0) (hL:∀i,torusL (y i)≠0)
    (hv:VacuumRegular (fun i =>torusWeights (y i))) :
    VacuumRegular (fun i =>torusWeights (x i)) := by
  apply vacuumRegular_of_rationalAt φ.toRingHom _ _ _ hv
  intro i t
  exact rationalAt_torusWeights φ (h i) (hy i) (hL i) t

def pairPoint (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (variableF 0) (Fin.cons (constF (n+1) phase^s*variableF 0) (fun i =>variableF i.succ))
lemma pairPoint_ne_zero (n s:ℕ) (i:Fin (n+2)) : pairPoint n s i≠0 := by
  induction i using Fin.cases with
  | zero => exact variableF_ne_zero 0
  | succ i => induction i using Fin.cases with
    | zero => exact mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero 0)
    | succ i => exact variableF_ne_zero i.succ

def pairEvaluation (n s:ℕ) : Laurent (n+2) →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (pairPoint n s) (pairPoint_ne_zero n s)

lemma rationalAt_pair_variable {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (variableF i) (pairPoint n s i) :=
  rationalAt_variable _ _ i

lemma torusL_phase_five (n:ℕ) : torusL (constF n phase^5)=0 := by
  unfold torusL
  rw [←pow_add,←pow_add]
  simp only [Nat.reduceAdd,torusSin_phase_pow]
  have he:(8:ℝ)*lambda=Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,he,Real.sin_pi,Complex.ofReal_zero,constF,map_zero,mul_zero]

lemma torusL_phase_six (n:ℕ) : torusL (constF n phase^6)=0 := by
  unfold torusL
  rw [←pow_add,←pow_add]
  simp only [Nat.reduceAdd,torusSin_phase_pow]
  have he:(8:ℝ)*lambda=Real.pi := by unfold lambda; ring
  simp only [Nat.cast_ofNat,he,Real.sin_pi,Complex.ofReal_zero,constF,map_zero,zero_mul]

lemma pairEvaluation_vacantNumerator {n:ℕ} (s:ℕ) (hs:s=2 ∨ s=3) :
    pairEvaluation n s (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)=0 := by
  have hv:RationalAt (pairEvaluation n s).toRingHom
      (constF (n+2) phase^3*(variableF (1:Fin (n+2))/variableF 0))
      (constF (n+1) phase^(s+3)) := by
    have hh:=((rationalAt_const (pairEvaluation n s) phase).pow 3).mul
      ((rationalAt_pair_variable s (1:Fin (n+2))).div (rationalAt_pair_variable s 0) (variableF_ne_zero 0))
    have he:constF (n+1) phase^3*(pairPoint n s 1 / pairPoint n s 0)=constF (n+1) phase^(s+3) := by
      change constF (n+1) phase^3*((constF (n+1) phase^s*variableF 0)/variableF 0)=_
      rw [mul_div_cancel_right₀ _ (variableF_ne_zero 0),pow_add,mul_comm]
    rwa [he] at hh
  have ht:=rationalAt_torusL _ hv (pow_ne_zero _ (constF_phase_ne_zero _))
  have ha:=RationalAt.algebraMap (φ:=(pairEvaluation n s).toRingHom) (F:=SpectralField (n+2))
    (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)
  change RationalAt _ (evalLaurent _) _ at ha
  rw [torusNumeratorL_pair_map] at ha
  change RationalAt _ (torusL _) _ at ha
  have hh:=ha.unique ht
  rcases hs with rfl | rfl
  · simpa using hh.trans (torusL_phase_five (n+1))
  · simpa using hh.trans (torusL_phase_six (n+1))


 

 


lemma torusL_phase_small_ne_zero (m k:ℕ) (hk:k≤3) :
    torusL (constF m phase^k)≠0 := by
  unfold torusL
  rw [←pow_add,←pow_add,torusSin_phase_pow,torusSin_phase_pow]
  apply mul_ne_zero <;> apply (map_ne_zero (algebraMap ℂ (SpectralField m))).mpr
  all_goals apply Complex.ofReal_ne_zero.mpr
  all_goals apply ne_of_gt; apply Real.sin_pos_of_pos_of_lt_pi
  all_goals unfold lambda; push_cast; nlinarith [Real.pi_pos,show (k:ℝ)≤3 by exact_mod_cast hk, Nat.cast_nonneg (α:=ℝ) k]

def allOneEvaluation (n:ℕ) : Laurent n →ₐ[ℂ] SpectralField 0 :=
  torusEvaluation (fun _ =>1) (fun _ =>one_ne_zero)

lemma rationalAt_phaseRow {n:ℕ} (i:Fin n) (k:ℕ) :
    RationalAt (allOneEvaluation n).toRingHom (constF n phase^k/variableF i) (constF 0 phase^k) := by
  simpa only [div_one] using ((rationalAt_const (allOneEvaluation n) phase).pow k).div
    (rationalAt_variable (fun _ : Fin n =>(1:SpectralField 0)) (fun _ =>one_ne_zero) i) one_ne_zero

lemma torusL_phaseRow_ne_zero {n:ℕ} (i:Fin n) (k:ℕ) (hk:k≤3) :
    torusL (constF n phase^k/variableF i)≠0 :=
  (rationalAt_torusL (allOneEvaluation n) (rationalAt_phaseRow i k)
    (pow_ne_zero _ (constF_phase_ne_zero 0))).ne_zero (torusL_phase_small_ne_zero 0 k hk)

 

lemma phaseRows_regular {n r:ℕ} (v:Fin r → Fin n) (k:Fin r → ℕ)
    (hk:∀j,k j≤3) (hm:∀i j, (k i≠0 ∧ k i≠3) → (k j≠0 ∧ k j≠3) → i=j) :
    VacuumRegular (fun j =>torusWeights (constF n phase^(k j)/variableF (v j))) := by
  apply torusRegular_of_rationalAt (allOneEvaluation n) _ (fun j =>constF 0 phase^(k j))
    (fun j =>rationalAt_phaseRow (v j) (k j))
    (fun j =>pow_ne_zero _ (constF_phase_ne_zero 0))
    (fun j =>torusL_phase_small_ne_zero 0 (k j) (hk j))
  unfold VacuumRegular
  rw [det_one_nonflat]
  · exact one_ne_zero
  · intro i j hi hj
    apply hm i j
    · constructor
      · intro h; apply hi; left; simp [h, torusWeights_one]
      · intro h; apply hi; right; rw [h,torusWeights_phase_three]
    · constructor
      · intro h; apply hj; left; simp [h,torusWeights_one]
      · intro h; apply hj; right; rw [h,torusWeights_phase_three]

end
end CriticalStrip.Diagram

end OAI
