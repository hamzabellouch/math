import Mathlib
import OAI.Combinatorics.StripMass.PairSelfNode

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma mappedNodal_leading {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (p:Pairing n) :
    ((P p.padTop).map (torusEvaluation z hz).toRingHom).coeff n=
      scalarValue (algebraMap ℂ (SpectralField m)) (fun i =>torusCos ((z i)^2/constF m phase^3))*
        normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p := by
  rw [Polynomial.coeff_map]
  have h:=RationalAt.algebraMap (φ:=(torusEvaluation z hz).toRingHom)
    (F:=SpectralField n) ((P p.padTop).coeff n)
  have he:=congrArg (fun Q:Polynomial (SpectralField n) =>Q.coeff n) (hP p.padTop)
  rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at he
  rw [he] at h
  exact h.unique (rationalAt_torusVacuum z hz hL hreg p)

lemma mappedNodal_degree {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (φ:Laurent n →+* SpectralField m) : LastDegree n (fun p =>(P p).map φ) := by
  exact (LastDegree.of_map (algebraMap (SpectralRing n) (SpectralField n)) (IsFractionRing.injective _ _)
    (by simpa only [hP] using rationalNodalPolynomial_degree n)).map φ

lemma lastValue_mul_poly {K:Type*} [CommRing K] {n:ℕ}
    (b s:K) (F:Polynomial K) (P:Pairing (n+1) → Polynomial K) :
    lastValue (RingHom.id K) b s (fun p =>F*P p)=F.eval b • lastValue (RingHom.id K) b s P := by
  funext p
  simp only [lastValue,Polynomial.eval₂_id,Polynomial.eval_mul,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

lemma mappedNodal_pair_node {n s:ℕ} (hs:s≤3)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (i:Fin (n+2)) (hi:i≠1) :
    lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n s i) (torusSin (deletionNode (pairIndex n i)))
      (fun p =>(P p).map (pairEvaluation n s).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i)) •
        normalizedVacuum (pairNodeWeights n s i) := by
  funext p
  have hsine:=rationalAt_torusSin (pairEvaluation n s) (rationalAt_pair_deletionNode s i)
    (mul_ne_zero (pairPoint_ne_zero n s i) (pow_ne_zero _ (constF_phase_ne_zero _)))
  rw [pairPoint_of_ne i hi] at hsine
  change RationalAt _ (torusSin (deletionNode i)) (torusSin (deletionNode (pairIndex n i))) at hsine
  have he:RationalAt (pairEvaluation n s).toRingHom
      ((rationalNodalPolynomial (n+2) p).eval (deletionBeta i))
      (((P p).map (pairEvaluation n s).toRingHom).eval (pairBeta n s i)) := by
    rw [←hP]
    exact RationalAt.eval_map _ (rationalAt_pair_deletionBeta s i) _
  have hsin:RationalAt (pairEvaluation n s).toRingHom
      (if p.Occupied (Fin.last (n+2)) then torusSin (deletionNode i) else 1)
      (if p.Occupied (Fin.last (n+2)) then torusSin (deletionNode (pairIndex n i)) else 1) := by
    split_ifs
    · exact hsine
    · exact RationalAt.one
  have hh:=hsin.mul he
  rw [rationalNodalPolynomial_at_node] at hh
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul] using
    hh.unique (rationalAt_pair_nodalVacuum hs i hi p)


 

 


lemma deletePoint_cosines (n:ℕ) :
    (fun i:Fin n =>torusCos ((deletePoint n i)^2/constF (n+1) phase^3))=
      fun i:Fin n =>fcos i.succ (-3) := by
  funext i
  have he:=phaseCosine i.succ 0
  norm_num only at he
  simpa only [deletePoint,zpow_zero,one_mul] using he

def deleteEvaluation (n:ℕ) : Laurent n →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (deletePoint n) (fun i =>variableF_ne_zero i.succ)

lemma deleteMapped_leading {n:ℕ}
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (p:Pairing n) :
    ((Q p.padTop).map (deleteEvaluation n).toRingHom).coeff n=
      scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3))*
        normalizedVacuum (deleteWeights n) p := by
  have h:=mappedNodal_leading Q hQ (deletePoint n) (fun i =>variableF_ne_zero i.succ)
    (fun i =>torusL_phaseRow_ne_zero i.succ 3 (by omega)) (deleteWeights_regular n) p
  rw [deletePoint_cosines] at h
  exact h

lemma deleteMapped_node {n:ℕ}
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (i:Fin (n+1)) :
    lastValue (RingHom.id (SpectralField (n+1))) (deletionBeta i) (torusSin (deletionNode i))
      (fun p =>(Q p).map (deleteEvaluation n).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta i)) •
          normalizedVacuum (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i) := by
  funext p
  have he:=lastLaurent_regular_value Q hQ (deletePoint n) (fun j =>variableF_ne_zero j.succ)
    (deletionNode i) (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero _))) (deletePoint_node_L i)
    (by rw [deletePoint_node_weights]; exact copiedNode_regular _ _) p
  have hc:(fun j =>torusCos (((Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)^2/constF (n+1) phase^3))=
      Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta i) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast j => simp only [Fin.snoc_castSucc]; exact congrFun (deletePoint_cosines n) j
  rw [hc,deletePoint_node_weights] at he
  change (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
    Polynomial.eval (deletionBeta i) ((Q p).map (deleteEvaluation n).toRingHom) = _ at he
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul,deleteEvaluation] using he

lemma pairMapped_delete_leading {n:ℕ}
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+2)) :
    ((P p.padTop).map (pairEvaluation n 3).toRingHom).coeff (n+2)=
      deletePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3))*
        (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (deleteWeights n)) p := by
  have hw:(fun i =>torusWeights (constF (n+1) phase^3/pairPoint n 3 i))=pairEarlierWeights n 3 :=
    funext (fun i =>congrArg torusWeights (pairArgument (by omega) i))
  have h:=mappedNodal_leading P hP (pairPoint n 3) (pairPoint_ne_zero n 3)
    (pairEarlier_L (by omega)) (by rw [hw]; exact pairEarlier_regular n 3) p
  rw [show (fun i =>torusCos ((pairPoint n 3 i)^2/constF (n+1) phase^3))=pairCosines n 3 from funext (fun i =>pairPoint_cosine i),
    hw,scalar_pair_delete,normalizedVacuum_pair_delete] at h
  exact h

def deletePairPolynomial (n:ℕ) : Polynomial (SpectralField (n+1)) :=
  Polynomial.C (deletePairScalar n)*((Polynomial.X-Polynomial.C (fcos 0 (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9)))

lemma deletePairPolynomial_degree (n:ℕ) : (deletePairPolynomial n).natDegree≤2 := by
  apply (Polynomial.natDegree_mul_le ..).trans
  simp only [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_mul_le ..).trans
  simp only [Polynomial.natDegree_X_sub_C]; omega

lemma deletePairPolynomial_top (n:ℕ) : (deletePairPolynomial n).coeff 2=deletePairScalar n := by
  rw [deletePairPolynomial,Polynomial.coeff_C_mul]
  have hp:(Polynomial.X-Polynomial.C (fcos (0:Fin (n+1)) (-9)))*(Polynomial.X-Polynomial.C (fcos 0 9))=
      Polynomial.X^2-Polynomial.C (fcos 0 (-9)+fcos 0 9)*Polynomial.X+Polynomial.C (fcos 0 (-9)*fcos 0 9) := by simp only [map_add,map_mul]; ring
  rw [hp]
  simp

lemma deletePairPolynomial_eval {n:ℕ} (b:SpectralField (n+1)) :
    (deletePairPolynomial n).eval b=deletePairScalar n*((b-fcos 0 (-9))*(b-fcos 0 9)) := by
  simp [deletePairPolynomial]


 

 


lemma phase_four_ne_one : phase^4≠(1:ℂ) := by
  intro h
  have hh:=congrArg (fun z:ℂ =>z^2) h
  rw [←pow_mul,show 4*2=8 by omega,phase_eight] at hh
  norm_num at hh

lemma pairBeta_head_ne {n s:ℕ} (hs:s=2 ∨ s=3) :
    deletionBeta (0:Fin (n+1))≠fcos 0 (2*(s:ℤ)+3) := by
  intro h
  rw [deletionBeta_shiftedCosine] at h
  have hh:=shiftedCosine_parameter 0 _ _ h
  rw [show 2*(s:ℤ)+3=3+2*s by ring,zpow_add₀ phase_ne_zero] at hh
  have he:phase^((2:ℤ)*s)=1 := mul_left_cancel₀ (zpow_ne_zero 3 phase_ne_zero) (by simpa using hh.symm)
  rcases hs with rfl|rfl
  · exact phase_four_ne_one (by simpa using he)
  · exact phase_six_ne_one (by simpa using he)

lemma pairBeta_injective (n s:ℕ) (hs:s=2 ∨ s=3) : Function.Injective (pairBeta n s) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨v,hv⟩
    induction v using Fin.cases with
    | zero => exact pairBeta_head_ne hs hv.symm
    | succ v => exact (deletionBeta_injective (n+1)).ne (Fin.succ_ne_zero v) hv
  · apply Fin.cons_injective_of_injective
    · rintro ⟨v,hv⟩
      change deletionBeta v.succ=fcos 0 (2*(s:ℤ)+3) at hv
      rw [deletionBeta_shiftedCosine] at hv
      exact shiftedCosine_ne v.succ 0 (Fin.succ_ne_zero v) _ _ (zpow_ne_zero _ phase_ne_zero) hv
    · exact (deletionBeta_injective (n+1)).comp (Fin.succ_injective n)


 

 


 

theorem rationalNodalPolynomial_pair_delete {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀p,evalLaurent (W p)=rationalVacuum (n+1) p)
    (Q:Pairing (n+1) → Polynomial (Laurent n))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hprev:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+1) p)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p) :
    (fun p =>(P p).map (pairEvaluation n 3).toRingHom)=
      fun p =>deletePairPolynomial n*
        matrixPolynomial (deletionMap 0 (show 2≤n+3 by omega))
          (fun q =>(Q q).map (deleteEvaluation n).toRingHom) p := by
  let Q':Pairing (n+1) → Polynomial (SpectralField (n+1)):=fun p =>(Q p).map (deleteEvaluation n).toRingHom
  let M:Matrix (Pairing (n+3)) (Pairing (n+1)) (SpectralField (n+1)):=deletionMap 0 (by omega)
  have hQd:LastDegree n Q':=mappedNodal_degree Q hQ _
  have hM:LastMatrix M:=deletionMap_last 0 (show 2≤n+2 by omega)
  have hMd:LastDegree n (matrixPolynomial M Q'):=hM.degree Q' hQd
  have hright:LastDegree (n+2) (fun p =>deletePairPolynomial n*matrixPolynomial M Q' p):=
    LastDegree.mul_poly _ hMd _ (deletePairPolynomial_degree n)
  apply lastPolynomial_unique _ _ (mappedNodal_degree P hP _) hright _ (pairBeta_injective n 3 (Or.inr rfl))
  · intro p
    rw [pairMapped_delete_leading P hP p]
    rw [LastDegree.mul_poly_top _ hMd _ (deletePairPolynomial_degree n) p,deletePairPolynomial_top]
    rw [hM.leading (deletionMap 0 (show 2≤n+2 by omega)) (fun p q =>deletionMap_padTop 0 (by omega) p q)]
    have he:(fun q:Pairing n =>(Q' q.padTop).coeff n)=
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun i:Fin n =>fcos i.succ (-3)) •
          normalizedVacuum (deleteWeights n) := funext (deleteMapped_leading Q hQ)
    rw [he,Matrix.mulVec_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  · intro p i
    by_cases hi:i=1
    · subst i
      rw [show pairBeta n 3 1=pairEvaluation n 3 (betaL 1) from (pairEvaluation_betaL 3 1).symm,
        rationalNodalPolynomial_pair_self W hW P hP 3 (Or.inr rfl)]
      rw [pairEvaluation_betaL,Polynomial.eval_mul,deletePairPolynomial_eval]
      change 0=deletePairScalar n*((fcos 0 9-fcos 0 (-9))*(fcos 0 9-fcos 0 9))*_
      ring
    · have he: lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 3 i) (torusSin (deletionNode (pairIndex n i)))
          (fun p =>(P p).map (pairEvaluation n 3).toRingHom)=
          lastValue (RingHom.id (SpectralField (n+1))) (pairBeta n 3 i) (torusSin (deletionNode (pairIndex n i)))
            (fun p =>deletePairPolynomial n*matrixPolynomial M Q' p) := by
        rw [mappedNodal_pair_node (by omega) P hP i hi,lastValue_mul_poly,hM.lastValue]
        rw [pairBeta_of_ne i hi,deleteMapped_node Q hprev]
        rw [Matrix.mulVec_smul,smul_smul]
        rw [normalizedVacuum_pairNode_delete,deletePairPolynomial_eval]
        have hs:=scalar_pair_delete_snoc (n:=n) (deletionBeta (pairIndex n i))
        rw [hs]
      have hp:=congrFun he p
      by_cases ho:p.Occupied (Fin.last (n+2))
      · simp only [lastValue,Polynomial.eval₂_id,ho,ite_true] at hp
        exact mul_left_cancel₀ (deletionNode_sine_ne_zero _) hp
      · simpa only [lastValue,Polynomial.eval₂_id,ho,ite_false] using hp


 

 


def mergeZ (n:ℕ) : SpectralField (n+1) := constF (n+1) phase/variableF 0
def mergePoint (n:ℕ) : Fin (n+1) → SpectralField (n+1) :=
  Fin.cons (constF (n+1) phase*variableF 0) (deletePoint n)
def mergeNewWeights (n:ℕ) : Fin (n+1) → Weights (SpectralField (n+1)) :=
  Fin.cons (torusWeights (constF (n+1) phase*mergeZ n)) (deleteWeights n)

def mergeExponent (n:ℕ) : Fin (n+1) → ℕ := Fin.cons 2 (fun _ =>3)

lemma mergeNewWeights_phase (n:ℕ) : mergeNewWeights n=
    fun i =>torusWeights (constF (n+1) phase^mergeExponent n i/variableF i) := by
  funext i
  induction i using Fin.cases with
  | zero => simp only [mergeNewWeights,Fin.cons_zero,mergeExponent,mergeZ]; congr 1; ring
  | succ i => rfl

lemma mergeExponent_le (n:ℕ) (i:Fin (n+1)) : mergeExponent n i≤3 := by
  induction i using Fin.cases <;> simp [mergeExponent]

lemma mergeExponent_mixed {n:ℕ} (i j:Fin (n+1))
    (hi:mergeExponent n i≠0 ∧ mergeExponent n i≠3)
    (hj:mergeExponent n j≠0 ∧ mergeExponent n j≠3) : i=j := by
  induction i using Fin.cases with
  | succ i => exact (hi.2 rfl).elim
  | zero => induction j using Fin.cases with
    | zero => rfl
    | succ j => exact (hj.2 rfl).elim

lemma mergeNewWeights_regular (n:ℕ) : VacuumRegular (mergeNewWeights n) := by
  rw [mergeNewWeights_phase]
  exact phaseRows_regular id (mergeExponent n) (mergeExponent_le n) mergeExponent_mixed

lemma mergeZ_ne_zero (n:ℕ) : mergeZ n≠0 := div_ne_zero (constF_phase_ne_zero _) (variableF_ne_zero _)
lemma mergeZ_L (n:ℕ) : torusL (mergeZ n)≠0 := by
  simpa only [mergeZ,pow_one] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 1 (by omega)
lemma mergeZ_one_L (n:ℕ) : torusL (constF (n+1) phase*mergeZ n)≠0 := by
  have he:constF (n+1) phase*mergeZ n=constF (n+1) phase^2/variableF 0 := by unfold mergeZ; ring
  rw [he]; exact torusL_phaseRow_ne_zero _ _ (by omega)
lemma mergeZ_two_L (n:ℕ) : torusL (constF (n+1) phase^2*mergeZ n)≠0 := by
  have he:constF (n+1) phase^2*mergeZ n=constF (n+1) phase^3/variableF 0 := by unfold mergeZ; ring
  rw [he]; exact torusL_phaseRow_ne_zero _ _ (by omega)

lemma pairEarlier_merge (n:ℕ) : pairEarlierWeights n 2=
    Fin.cons (torusWeights (constF (n+1) phase^2*mergeZ n))
      (Fin.cons (torusWeights (mergeZ n)) (deleteWeights n)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      simp only [pairEarlierWeights,pairExponent,pairIndex,Fin.cons_zero]
      rw [ite_eq_right (by intro h; have := congrArg Fin.val h; simp at this)]
      congr 1; unfold mergeZ; ring
  | succ i => induction i using Fin.cases with
    | zero => simp [pairEarlierWeights,pairExponent,pairIndex,mergeZ]
    | succ i =>
      have hi : i.succ.succ≠(1:Fin (n+2)) := by intro h; have := congrArg Fin.val h; simp at this
      simp [pairEarlierWeights,pairExponent,pairIndex,hi,deleteWeights]

lemma normalizedVacuum_pair_merge (n:ℕ) :
    normalizedVacuum (pairEarlierWeights n 2)=
      (mergeMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (mergeNewWeights n)) := by
  have h:=normalizedVacuum_merge_cons (deleteWeights n) (mergeZ n) (mergeZ_ne_zero n)
    (mergeZ_L n) (mergeZ_one_L n) (mergeZ_two_L n)
    (by rw [←pairEarlier_merge]; exact pairEarlier_regular n 2) (mergeNewWeights_regular n)
  rwa [←pairEarlier_merge] at h

lemma mergePoint_ne_zero (n:ℕ) (i:Fin (n+1)) : mergePoint n i≠0 := by
  induction i using Fin.cases with
  | zero => exact mul_ne_zero (constF_phase_ne_zero _) (variableF_ne_zero _)
  | succ i => exact variableF_ne_zero _

lemma mergePoint_weights (n:ℕ) :
    (fun i =>torusWeights (constF (n+1) phase^3/mergePoint n i))=mergeNewWeights n := by
  funext i
  induction i using Fin.cases with
  | zero =>
      change torusWeights (constF (n+1) phase^3/(constF (n+1) phase*variableF 0))=_
      change _=torusWeights (constF (n+1) phase*(constF (n+1) phase/variableF 0))
      congr 1
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | succ i => rfl

lemma mergePoint_argument (n:ℕ) (i:Fin (n+1)) :
    constF (n+1) phase^3/mergePoint n i=constF (n+1) phase^(mergeExponent n i)/variableF i := by
  induction i using Fin.cases with
  | zero =>
      change constF (n+1) phase^3/(constF (n+1) phase*variableF 0)=constF (n+1) phase^2/variableF 0
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | succ i => rfl

lemma mergePoint_L (n:ℕ) (i:Fin (n+1)) : torusL (constF (n+1) phase^3/mergePoint n i)≠0 := by
  rw [mergePoint_argument]
  exact torusL_phaseRow_ne_zero i _ (mergeExponent_le n i)

lemma mergePoint_cosines (n:ℕ) :
    (fun i =>torusCos ((mergePoint n i)^2/constF (n+1) phase^3))=
      Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)) := by
  funext i
  induction i using Fin.cases with
  | zero =>
      have he:=phaseCosine (0:Fin (n+1)) 1
      norm_num only at he
      simpa only [mergePoint,Fin.cons_zero,zpow_one] using he
  | succ i =>
      have he:=phaseCosine i.succ 0
      norm_num only at he
      simpa only [mergePoint,deletePoint,Fin.cons_succ,zpow_zero,one_mul] using he


 

 


def mergeNodeWeights {n:ℕ} (i:Fin (n+1)) : Fin (n+2) → Weights (SpectralField (n+1)) :=
  Fin.snoc (mergeNewWeights n) (torusWeights ((variableF i)⁻¹))

lemma mergeNode_regular {n:ℕ} (i:Fin (n+1)) : VacuumRegular (mergeNodeWeights i) := by
  have hw:mergeNodeWeights i=fun j =>torusWeights
      (constF (n+1) phase^((Fin.snoc (mergeExponent n) 0 : Fin (n+2) → ℕ) j)/
        variableF ((Fin.snoc id i : Fin (n+2) → Fin (n+1)) j)) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [mergeNodeWeights]
    | cast j => simpa only [mergeNodeWeights,Fin.snoc_castSucc,id_eq] using congrFun (mergeNewWeights_phase n) j
  rw [hw]
  apply phaseRows_regular
  · intro j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simpa only [Fin.snoc_castSucc] using mergeExponent_le n j
  · intro j k hj hk
    induction j using Fin.lastCases with
    | last => exact (hj.1 (by simp)).elim
    | cast j => induction k using Fin.lastCases with
      | last => exact (hk.1 (by simp)).elim
      | cast k =>
        simp only [Fin.snoc_castSucc] at hj hk
        exact congrArg Fin.castSucc (mergeExponent_mixed j k hj hk)

lemma pairNode_merge {n:ℕ} (i:Fin (n+2)) : pairNodeWeights n 2 i=
    Fin.cons (torusWeights (constF (n+1) phase^2*mergeZ n))
      (Fin.cons (torusWeights (mergeZ n))
        (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  rw [pairNodeWeights,pairEarlier_merge]
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma mergeNode_cons {n:ℕ} (i:Fin (n+1)) : mergeNodeWeights i=
    Fin.cons (torusWeights (constF (n+1) phase*mergeZ n))
      (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i) := by
  unfold mergeNodeWeights mergeNewWeights
  rw [←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma normalizedVacuum_pairNode_merge {n:ℕ} (i:Fin (n+2)) :
    normalizedVacuum (pairNodeWeights n 2 i)=
      (mergeMap 0 (show 2≤n+3 by omega)).mulVec
        (normalizedVacuum (mergeNodeWeights (pairIndex n i))) := by
  rw [pairNode_merge,mergeNode_cons]
  exact normalizedVacuum_merge_cons (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))
    (mergeZ n) (mergeZ_ne_zero n) (mergeZ_L n) (mergeZ_one_L n) (mergeZ_two_L n)
    (by rw [←pairNode_merge i]; exact pairNode_regular n 2 i)
    (by rw [←mergeNode_cons]; exact mergeNode_regular _)

lemma mergePoint_node_weights {n:ℕ} (i:Fin (n+1)) :
    (fun j =>torusWeights (constF (n+1) phase^3/
      (Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)) =mergeNodeWeights i := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last,mergeNodeWeights]
      congr 1
      rw [deletionNode]
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | cast j => simpa only [Fin.snoc_castSucc,mergeNodeWeights] using congrFun (mergePoint_weights n) j

lemma mergePoint_node_L {n:ℕ} (i:Fin (n+1)) (j:Fin (n+2)) :
    torusL (constF (n+1) phase^3/
      (Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)≠0 := by
  induction j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      have he:constF (n+1) phase^3/deletionNode i=(variableF i)⁻¹ := by
        rw [deletionNode]; field_simp [constF_phase_ne_zero,variableF_ne_zero]
      rw [he]
      simpa using torusL_phaseRow_ne_zero i 0 (by omega)
  | cast j => simpa only [Fin.snoc_castSucc] using mergePoint_L n j


 

 


def mergeEvaluation (n:ℕ) : Laurent (n+1) →ₐ[ℂ] SpectralField (n+1) :=
  torusEvaluation (mergePoint n) (mergePoint_ne_zero n)

lemma mergeMapped_leading {n:ℕ}
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,(Q p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+1)) :
    ((Q p.padTop).map (mergeEvaluation n).toRingHom).coeff (n+1)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*
        normalizedVacuum (mergeNewWeights n) p := by
  have h:=mappedNodal_leading Q hQ (mergePoint n) (mergePoint_ne_zero n)
    (mergePoint_L n) (by rw [mergePoint_weights]; exact mergeNewWeights_regular n) p
  rw [mergePoint_cosines,mergePoint_weights] at h
  exact h

lemma mergeMapped_node {n:ℕ}
    (Q:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hQ:∀p,evalLaurent (lastLaurent p (Q p))=rationalVacuum (n+2) p)
    (i:Fin (n+1)) :
    lastValue (RingHom.id (SpectralField (n+1))) (deletionBeta i) (torusSin (deletionNode i))
      (fun p =>(Q p).map (mergeEvaluation n).toRingHom)=
      scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (deletionBeta i)) •
          normalizedVacuum (mergeNodeWeights i) := by
  funext p
  have he:=lastLaurent_regular_value Q hQ (mergePoint n) (mergePoint_ne_zero n)
    (deletionNode i) (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero _))) (mergePoint_node_L i)
    (by rw [mergePoint_node_weights]; exact mergeNode_regular _) p
  have hc:(fun j =>torusCos (((Fin.snoc (mergePoint n) (deletionNode i) : Fin (n+2) → SpectralField (n+1)) j)^2/constF (n+1) phase^3))=
      Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (deletionBeta i) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast j => simp only [Fin.snoc_castSucc]; exact congrFun (mergePoint_cosines n) j
  rw [hc,mergePoint_node_weights] at he
  change (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) *
    Polynomial.eval (deletionBeta i) ((Q p).map (mergeEvaluation n).toRingHom) = _ at he
  simpa only [lastValue,Polynomial.eval₂_id,Pi.smul_apply,smul_eq_mul,ite_mul,one_mul,mergeEvaluation] using he

lemma pairMapped_merge_leading {n:ℕ}
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (p:Pairing (n+2)) :
    ((P p.padTop).map (pairEvaluation n 2).toRingHom).coeff (n+2)=
      mergePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun i:Fin n =>fcos i.succ (-3)))*
        (mergeMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (mergeNewWeights n)) p := by
  have hw:(fun i =>torusWeights (constF (n+1) phase^3/pairPoint n 2 i))=pairEarlierWeights n 2 :=
    funext (fun i =>congrArg torusWeights (pairArgument (by omega) i))
  have h:=mappedNodal_leading P hP (pairPoint n 2) (pairPoint_ne_zero n 2)
    (pairEarlier_L (by omega)) (by rw [hw]; exact pairEarlier_regular n 2) p
  rw [show (fun i =>torusCos ((pairPoint n 2 i)^2/constF (n+1) phase^3))=pairCosines n 2 from funext (fun i =>pairPoint_cosine i),
    hw,scalar_pair_merge,normalizedVacuum_pair_merge] at h
  exact h

def mergePairPolynomial (n:ℕ) : Polynomial (SpectralField (n+1)) :=
  Polynomial.C (mergePairScalar n)*(Polynomial.X+Polynomial.C (fcos 0 (-1)))

lemma mergePairPolynomial_degree (n:ℕ) : (mergePairPolynomial n).natDegree≤1 := by
  apply (Polynomial.natDegree_mul_le ..).trans
  simp

lemma mergePairPolynomial_top (n:ℕ) : (mergePairPolynomial n).coeff 1=mergePairScalar n := by
  simp [mergePairPolynomial]

lemma mergePairPolynomial_eval {n:ℕ} (b:SpectralField (n+1)) :
    (mergePairPolynomial n).eval b=mergePairScalar n*(b+fcos 0 (-1)) := by
  simp [mergePairPolynomial]

end
end CriticalStrip.Diagram

end OAI
