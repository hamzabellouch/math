import Mathlib
import OAI.Combinatorics.StripMass.ScalarMergeTrig
import OAI.Combinatorics.StripMass.FirstThree

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma matrixPrefix_zero_of_first {K ι:Type*} [CommRing K] [Fintype ι] [DecidableEq ι]
    {n:ℕ} (A:Fin (n+1) → Matrix ι ι K) (h:A 0=0) (k:ℕ) :
    matrixPrefix A (k+1)=0 := by
  induction k with
  | zero => simpa [matrixPrefix] using h
  | succ k ih => rw [matrixPrefix]; split_ifs <;> simp only [ih,Matrix.mul_zero]

lemma reducedMovingStepL_pair_zero {n:ℕ} (s:ℕ) (hs:s=2 ∨ s=3) :
    (reducedMovingStepL (1:Fin (n+2)) 0).map (pairEvaluation n s).toRingHom=0 := by
  simp only [reducedMovingStepL,show (0:Fin (n+2))≠1 by intro h; have := congrArg Fin.val h; simp at this,ite_false,
    show ¬(1:Fin (n+2))<0 from not_lt_of_ge (Fin.zero_le _)]
  rw [matrix_map_ring_smul,matrix_map_ring_smul]
  rw [show (pairEvaluation n s).toRingHom
      (torusNumeratorL (variableExponent (1:Fin (n+2))-variableExponent 0) (phase^3) .vacant)=0 from pairEvaluation_vacantNumerator s hs]
  simp

lemma nodalDatumL_pair_self_zero {n:ℕ} (W:Pairing (n+1) → Laurent (n+1))
    (s:ℕ) (hs:s=2 ∨ s=3) (p:Pairing (n+3)) :
    pairEvaluation n s (nodalDatumL W (1:Fin (n+2)) p)=0 := by
  simp only [nodalDatumL,map_mul]
  have hm:(matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).map (pairEvaluation n s).toRingHom=0 := by
    rw [matrixPrefix_map]
    exact matrixPrefix_zero_of_first _ (reducedMovingStepL_pair_zero s hs) (n+1)
  rw [show pairEvaluation n s
      ((matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).mulVec _ p)=
      ((matrixPrefix (reducedMovingStepL (1:Fin (n+2))) (n+2)).map (pairEvaluation n s).toRingHom).mulVec _ p from
      RingHom.map_mulVec _ _ _ p]
  rw [hm,Matrix.zero_mulVec]
  simp

lemma rationalNodalPolynomial_laurent_at_node {n:ℕ}
    (W:Pairing n → Laurent n) (hW:∀q,evalLaurent (W q)=rationalVacuum n q)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (p:Pairing (n+2)) (i:Fin (n+1)) :
    (P p).eval (betaL i)=nodalDatumL W i p := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent ((P p).eval (betaL i))=evalLaurent (nodalDatumL W i p)
  rw [nodalDatumL_map W hW]
  have hh:=rationalNodalPolynomial_at_node p i
  rw [eq_div_iff (by split_ifs; exact deletionNode_sine_ne_zero i; exact one_ne_zero)]
  rw [mul_comm]
  rw [←hP] at hh
  have hf:evalLaurent ((P p).eval (betaL i))=
      ((P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).eval (deletionBeta i) := by
    rw [←betaL_map]
    exact (Polynomial.eval_map_apply ..).symm
  rw [hf]
  exact hh

 

theorem rationalNodalPolynomial_pair_self {n:ℕ}
    (W:Pairing (n+1) → Laurent (n+1)) (hW:∀q,evalLaurent (W q)=rationalVacuum (n+1) q)
    (P:Pairing (n+3) → Polynomial (Laurent (n+2)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+2)) (SpectralField (n+2)))=rationalNodalPolynomial (n+2) p)
    (s:ℕ) (hs:s=2 ∨ s=3) (p:Pairing (n+3)) :
    ((P p).map (pairEvaluation n s).toRingHom).eval (pairEvaluation n s (betaL 1))=0 := by
  change ((P p).map (pairEvaluation n s).toRingHom).eval ((pairEvaluation n s).toRingHom (betaL 1))=0
  rw [Polynomial.eval_map_apply,rationalNodalPolynomial_laurent_at_node W hW P hP]
  exact nodalDatumL_pair_self_zero W s hs p


 

 


def pairIndex (n:ℕ) : Fin (n+2) → Fin (n+1) := Fin.cons 0 (Fin.cons 0 Fin.succ)
def pairExponent (n s:ℕ) : Fin (n+2) → ℕ := fun i =>if i=1 then 3-s else 3

def pairEarlierWeights (n s:ℕ) : Fin (n+2) → Weights (SpectralField (n+1)) :=
  fun j =>torusWeights (constF (n+1) phase^(pairExponent n s j)/variableF (pairIndex n j))

def pairNodeWeights (n s:ℕ) (i:Fin (n+2)) : Fin (n+3) → Weights (SpectralField (n+1)) :=
  Fin.snoc (pairEarlierWeights n s) (torusWeights (variableF (pairIndex n i))⁻¹)

lemma pairExponent_le (n s:ℕ) (i:Fin (n+2)) : pairExponent n s i≤3 := by
  unfold pairExponent; split_ifs <;> omega

lemma pairExponent_mixed {n s:ℕ} (i j:Fin (n+2))
    (hi:pairExponent n s i≠0 ∧ pairExponent n s i≠3)
    (hj:pairExponent n s j≠0 ∧ pairExponent n s j≠3) : i=j := by
  have h₁:i=1 := by by_contra h; exact hi.2 (ite_eq_right h)
  have h₂:j=1 := by by_contra h; exact hj.2 (ite_eq_right h)
  exact h₁.trans h₂.symm

lemma pairEarlier_regular (n s:ℕ) : VacuumRegular (pairEarlierWeights n s) :=
  phaseRows_regular (pairIndex n) (pairExponent n s) (pairExponent_le n s) pairExponent_mixed

lemma pairNode_regular (n s:ℕ) (i:Fin (n+2)) : VacuumRegular (pairNodeWeights n s i) := by
  have h:=phaseRows_regular (Fin.snoc (pairIndex n) (pairIndex n i))
    (Fin.snoc (pairExponent n s) 0)
    (fun j =>Fin.lastCases (by simp) (fun j =>by simpa using pairExponent_le n s j) j) ?_
  · convert h using 1
    funext j
    induction j using Fin.lastCases <;> simp [pairNodeWeights,pairEarlierWeights]
  · intro j k hj hk
    induction j using Fin.lastCases with
    | last => exact (hj.1 (by simp)).elim
    | cast j => induction k using Fin.lastCases with
      | last => exact (hk.1 (by simp)).elim
      | cast k => exact congrArg Fin.castSucc (pairExponent_mixed (s:=s) j k (by simpa using hj) (by simpa using hk))

lemma pairPoint_of_ne {n s:ℕ} (i:Fin (n+2)) (hi:i≠1) :
    pairPoint n s i=variableF (pairIndex n i) := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => induction i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i => rfl

lemma pairArgument {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) :
    constF (n+1) phase^3/pairPoint n s i=
      constF (n+1) phase^(pairExponent n s i)/variableF (pairIndex n i) := by
  by_cases hi:i=1
  · subst i
    change constF (n+1) phase^3/(constF (n+1) phase^s*variableF 0)=constF (n+1) phase^(if (1:Fin (n+2))=1 then 3-s else 3)/variableF 0
    rw [ite_eq_left rfl]
    have hp:constF (n+1) phase^(3-s)*constF (n+1) phase^s=constF (n+1) phase^3 := by rw [←pow_add,Nat.sub_add_cancel hs]
    apply (div_eq_div_iff (mul_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)) (variableF_ne_zero _)).mpr
    rw [←hp]; ring
  · rw [pairPoint_of_ne i hi,pairExponent,ite_eq_right hi]

lemma pairEarlier_L {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) :
    torusL (constF (n+1) phase^3/pairPoint n s i)≠0 := by
  rw [pairArgument hs i]
  exact torusL_phaseRow_ne_zero _ _ (pairExponent_le n s i)

lemma rationalAt_pair_nodalWeights {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) (hi:i≠1)
    (j:Fin (n+3)) (t:Tile) :
    RationalAt (pairEvaluation n s).toRingHom ((nodalWeights i j).tile t) ((pairNodeWeights n s i j).tile t) := by
  induction j using Fin.lastCases with
  | cast j =>
    simp only [nodalWeights,Fin.snoc_castSucc,spectralWeights,pairNodeWeights,pairEarlierWeights]
    rw [←pairArgument hs j]
    exact rationalAt_torusWeights _
      (((rationalAt_const (pairEvaluation n s) phase).pow 3).div (rationalAt_pair_variable s j) (pairPoint_ne_zero n s j))
      (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (pairPoint_ne_zero n s j)) (pairEarlier_L hs j) t
  | last =>
    simp only [nodalWeights_last,pairNodeWeights,Fin.snoc_last]
    have hv:=rationalAt_pair_variable s i
    rw [pairPoint_of_ne i hi] at hv
    exact rationalAt_torusWeights _ (hv.inv (variableF_ne_zero _))
      (inv_ne_zero (variableF_ne_zero _))
      (by simpa only [pow_zero,one_div] using torusL_phaseRow_ne_zero (pairIndex n i) 0 (by omega)) t


 

 


lemma phaseCosine {n:ℕ} (i:Fin n) (s:ℤ) :
    torusCos ((constF n phase^s*variableF i)^2/constF n phase^3)=fcos i (2*s-3) := by
  rw [fcos_eq,show 2*s-3=s*2-3 by ring,zpow_sub₀ phase_ne_zero,zpow_mul]
  simp only [constF,map_div₀,map_pow,map_zpow₀,zpow_ofNat]
  congr 1
  ring

def pairCosines (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (fcos 0 (-3)) (Fin.cons (fcos 0 (2*(s:ℤ)-3)) (fun i =>fcos i.succ (-3)))
def pairBeta (n s:ℕ) : Fin (n+2) → SpectralField (n+1) :=
  Fin.cons (deletionBeta 0) (Fin.cons (fcos 0 (2*(s:ℤ)+3)) (fun i =>deletionBeta i.succ))

lemma pairPoint_cosine {n s:ℕ} (i:Fin (n+2)) :
    torusCos ((pairPoint n s i)^2/constF (n+1) phase^3)=pairCosines n s i := by
  induction i using Fin.cases with
  | zero => simpa only [pairPoint,pairCosines,Fin.cons_zero,zpow_zero,one_mul,Int.mul_zero,Int.zero_sub] using phaseCosine (0:Fin (n+1)) 0
  | succ i => induction i using Fin.cases with
    | zero => simpa only [pairPoint,pairCosines,Fin.cons_succ,Fin.cons_zero,zpow_natCast] using phaseCosine (0:Fin (n+1)) (s:ℤ)
    | succ i => simpa only [pairPoint,pairCosines,Fin.cons_succ,zpow_zero,one_mul,Int.mul_zero,Int.zero_sub] using phaseCosine i.succ 0

lemma pairNode_cosine {n s:ℕ} (i:Fin (n+2)) :
    torusCos ((pairPoint n s i*constF (n+1) phase^3)^2/constF (n+1) phase^3)=pairBeta n s i := by
  induction i using Fin.cases with
  | zero => rfl
  | succ i => induction i using Fin.cases with
    | zero =>
      change torusCos (((constF (n+1) phase^s*variableF 0)*constF (n+1) phase^3)^2/constF (n+1) phase^3)=_
      have he:(constF (n+1) phase^s*variableF 0)*constF (n+1) phase^3=constF (n+1) phase^((s:ℤ)+3)*variableF 0 := by
        rw [zpow_add₀ (constF_phase_ne_zero _),zpow_natCast,zpow_ofNat]; ring
      rw [he,phaseCosine]
      change fcos 0 (2*((s:ℤ)+3)-3)=fcos 0 (2*(s:ℤ)+3)
      congr 1; ring
    | succ i => rfl

lemma rationalAt_pair_spectralA {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (spectralA i) (pairCosines n s i) := by
  rw [←pairPoint_cosine i]
  exact rationalAt_torusCos _ (((rationalAt_pair_variable s i).pow 2).div
    ((rationalAt_const (pairEvaluation n s) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (pairPoint_ne_zero n s i)) (pow_ne_zero _ (constF_phase_ne_zero _)))

lemma rationalAt_pair_deletionNode {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (deletionNode i)
      (pairPoint n s i*constF (n+1) phase^3) :=
  (rationalAt_pair_variable s i).mul ((rationalAt_const (pairEvaluation n s) phase).pow 3)

lemma rationalAt_pair_deletionBeta {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (deletionBeta i) (pairBeta n s i) := by
  rw [←pairNode_cosine i]
  exact rationalAt_torusCos _ (((rationalAt_pair_deletionNode s i).pow 2).div
    ((rationalAt_const (pairEvaluation n s) phase).pow 3) (pow_ne_zero _ (constF_phase_ne_zero _)))
    (div_ne_zero (pow_ne_zero _ (mul_ne_zero (pairPoint_ne_zero n s i) (pow_ne_zero _ (constF_phase_ne_zero _))))
      (pow_ne_zero _ (constF_phase_ne_zero _)))

lemma pairEvaluation_betaL {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    pairEvaluation n s (betaL i)=pairBeta n s i := by
  have h:=RationalAt.algebraMap (φ:=(pairEvaluation n s).toRingHom) (F:=SpectralField (n+2)) (betaL i)
  change RationalAt _ (evalLaurent (betaL i)) _ at h
  rw [betaL_map] at h
  exact h.unique (rationalAt_pair_deletionBeta s i)

lemma pairBeta_of_ne {n s:ℕ} (i:Fin (n+2)) (hi:i≠1) : pairBeta n s i=deletionBeta (pairIndex n i) := by
  rw [←pairNode_cosine i,pairPoint_of_ne i hi]
  rfl

lemma rationalAt_pair_nodalScalar {n:ℕ} (s:ℕ) (i:Fin (n+2)) :
    RationalAt (pairEvaluation n s).toRingHom (nodalScalar i)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i))) := by
  apply rationalAt_scalarValue
  intro j
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using rationalAt_pair_deletionBeta s i
  | cast j => simpa only [Fin.snoc_castSucc] using rationalAt_pair_spectralA s j

lemma rationalAt_pair_nodalVacuum {n s:ℕ} (hs:s≤3) (i:Fin (n+2)) (hi:i≠1) (p:Pairing (n+3)) :
    RationalAt (pairEvaluation n s).toRingHom (nodalVacuum i p)
      (scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n s) (pairBeta n s i))*
        normalizedVacuum (pairNodeWeights n s i) p) :=
  (rationalAt_pair_nodalScalar s i).mul
    (rationalAt_normalizedVacuum _ _ (rationalAt_pair_nodalWeights hs i hi) (pairNode_regular n s i) p)


 

 


lemma twoRows_omit_one {K:Type*} {n:ℕ} (a b d e:Weights K) (w:Fin n → Weights K) :
    (fun j =>(PartialColumn.twoRows (Fin.cons a (Fin.cons b w)) 0 d e)
      ((1:Fin (n+2)).succAbove j))=Fin.cons d w := by
  funext j
  induction j using Fin.cases with
  | zero => simp [PartialColumn.twoRows,Fin.succAbove]
  | succ j => simp [PartialColumn.twoRows,Fin.succAbove,Fin.lt_def]

lemma omit_first_two {α:Type*} {n:ℕ} (a b:α) (w:Fin n → α) :
    (fun j =>(Fin.cons a (Fin.cons b w) : Fin (n+2) → α)
      ((1:Fin (n+2)).succAbove ((0:Fin (n+1)).succAbove j)))=w := by
  funext j
  simp [Fin.succAbove,Fin.lt_def]

lemma normalizedVacuum_merge_cons {n m:ℕ} (w:Fin n → Weights (SpectralField m))
    (z:SpectralField m) (hz:z≠0) (hL:torusL z≠0)
    (hL1:torusL (constF m phase*z)≠0) (hL2:torusL (constF m phase^2*z)≠0)
    (hr:VacuumRegular (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w)))
    (hr':VacuumRegular (Fin.cons (torusWeights (constF m phase*z)) w)) :
    normalizedVacuum (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w))=
      (mergeMap 0 (show 2≤n+2 by omega)).mulVec
        (normalizedVacuum (Fin.cons (torusWeights (constF m phase*z)) w)) := by
  have he:=normalizedVacuum_merge 0 (show 2≤n+2 by omega)
    (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w))
    z hz hL hL1 hL2 rfl rfl hr
  have hrows : (fun i => PartialColumn.twoRows
      (Fin.cons (torusWeights (constF m phase^2*z)) (Fin.cons (torusWeights z) w)) 0
      (torusWeights (constF m phase*z)) swapWeights
      ((⟨0+1,by omega⟩ : Fin (n+2)).succAbove i)) = Fin.cons (torusWeights (constF m phase*z)) w :=
    twoRows_omit_one _ _ _ _ _
  rw [hrows] at he
  exact he hr'

lemma normalizedVacuum_deletion_cons {n m:ℕ} (w:Fin n → Weights (SpectralField m))
    (z:SpectralField m) (hz:z≠0) (hL:torusL z≠0) (hL3:torusL (constF m phase^3*z)≠0)
    (hr:VacuumRegular (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w)))
    (hr':VacuumRegular w) :
    normalizedVacuum (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w))=
      (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum w) := by
  have he:=normalizedVacuum_deletion 0 (show 2≤n+2 by omega)
    (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w))
    z hz hL hL3 rfl rfl hr
  have hrows : (fun i:Fin n => (Fin.cons (torusWeights (constF m phase^3*z)) (Fin.cons (torusWeights z) w) : Fin (n+2) → Weights (SpectralField m))
      ((⟨0+1,by omega⟩ : Fin (n+2)).succAbove ((⟨0,by omega⟩ : Fin (n+1)).succAbove i))) = w :=
    by funext i; simp [Fin.succAbove,Fin.lt_def]
  rw [hrows] at he
  exact he hr'


 

 


def deletePoint (n:ℕ) : Fin n → SpectralField (n+1) := fun i =>variableF i.succ

def deleteWeights (n:ℕ) : Fin n → Weights (SpectralField (n+1)) :=
  fun i =>torusWeights (constF (n+1) phase^3/variableF i.succ)

lemma deleteWeights_regular (n:ℕ) : VacuumRegular (deleteWeights n) :=
  phaseRows_regular Fin.succ (fun _ =>3) (by intros; omega) (by intros i j hi; exact (hi.2 rfl).elim)

lemma pairEarlier_delete (n:ℕ) : pairEarlierWeights n 3=
    Fin.cons (torusWeights (constF (n+1) phase^3*(variableF 0)⁻¹))
      (Fin.cons (torusWeights ((variableF 0)⁻¹)) (deleteWeights n)) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [pairEarlierWeights,pairExponent,pairIndex,div_eq_mul_inv]
  | succ i => induction i using Fin.cases with
    | zero => simp [pairEarlierWeights,pairExponent,pairIndex]
    | succ i =>
      have hi : i.succ.succ≠(1:Fin (n+2)) := by intro h; have := congrArg Fin.val h; simp at this
      simp [pairEarlierWeights,pairExponent,pairIndex,hi,deleteWeights]

lemma normalizedVacuum_pair_delete (n:ℕ) :
    normalizedVacuum (pairEarlierWeights n 3)=
      (deletionMap 0 (show 2≤n+2 by omega)).mulVec (normalizedVacuum (deleteWeights n)) := by
  have h:=normalizedVacuum_deletion_cons (deleteWeights n) ((variableF (0:Fin (n+1)))⁻¹)
    (inv_ne_zero (variableF_ne_zero _))
    (by simpa using torusL_phaseRow_ne_zero (0:Fin (n+1)) 0 (by omega))
    (by simpa only [div_eq_mul_inv] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 3 (by omega))
    (by rw [←pairEarlier_delete]; exact pairEarlier_regular n 3) (deleteWeights_regular n)
  rwa [←pairEarlier_delete] at h

lemma pairNode_delete {n:ℕ} (i:Fin (n+2)) : pairNodeWeights n 3 i=
    Fin.cons (torusWeights (constF (n+1) phase^3*(variableF 0)⁻¹))
      (Fin.cons (torusWeights ((variableF 0)⁻¹))
        (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  rw [pairNodeWeights,pairEarlier_delete]
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]
  rfl

lemma normalizedVacuum_pairNode_delete {n:ℕ} (i:Fin (n+2)) :
    normalizedVacuum (pairNodeWeights n 3 i)=
      (deletionMap 0 (show 2≤n+3 by omega)).mulVec
        (normalizedVacuum (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))) := by
  have h:=normalizedVacuum_deletion_cons (copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) (pairIndex n i))
    ((variableF (0:Fin (n+1)))⁻¹) (inv_ne_zero (variableF_ne_zero _))
    (by simpa using torusL_phaseRow_ne_zero (0:Fin (n+1)) 0 (by omega))
    (by simpa only [div_eq_mul_inv] using torusL_phaseRow_ne_zero (0:Fin (n+1)) 3 (by omega))
    (by rw [←pairNode_delete i]; exact pairNode_regular n 3 i) (copiedNode_regular _ _)
  rwa [←pairNode_delete i] at h

lemma deletePoint_node_weights {n:ℕ} (i:Fin (n+1)) :
    (fun j =>torusWeights (constF (n+1) phase^3/
      (Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)) =
      copiedNodeWeights (Fin.succ : Fin n → Fin (n+1)) i := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      simp only [Fin.snoc_last,copiedNodeWeights]
      congr 1
      rw [deletionNode]
      field_simp [constF_phase_ne_zero,variableF_ne_zero]
  | cast j => simp only [Fin.snoc_castSucc,copiedNodeWeights,deletePoint,spectralWeights]

lemma deletePoint_node_L {n:ℕ} (i:Fin (n+1)) (j:Fin (n+1)) :
    torusL (constF (n+1) phase^3/
      (Fin.snoc (deletePoint n) (deletionNode i) : Fin (n+1) → SpectralField (n+1)) j)≠0 := by
  induction j using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      have he:constF (n+1) phase^3/deletionNode i=(variableF i)⁻¹ := by
        rw [deletionNode]; field_simp [constF_phase_ne_zero,variableF_ne_zero]
      rw [he]
      simpa using torusL_phaseRow_ne_zero i 0 (by omega)
  | cast j => simpa only [Fin.snoc_castSucc,deletePoint] using torusL_phaseRow_ne_zero j.succ 3 (by omega)


 

 


lemma Fin.snoc_twoCons {α:Type*} {n:ℕ} (a b y:α) (x:Fin n → α) :
    (Fin.snoc (Fin.cons a (Fin.cons b x)) y : Fin (n+3) → α)=(Fin.cons a (Fin.cons b (Fin.snoc x y)) : Fin (n+3) → α) := by
  rw [←Fin.cons_snoc_eq_snoc_cons,←Fin.cons_snoc_eq_snoc_cons]

def deletePairScalar (n:ℕ) : SpectralField (n+1) :=
  (fcos 0 (-3)+fcos 0 3+constF (n+1) rho)*
    ∏j:Fin n,(fcos j.succ (-3)-fcos 0 (-9))*(fcos j.succ (-3)-fcos 0 9)

def mergePairScalar (n:ℕ) : SpectralField (n+1) :=
  (fcos 0 (-3)+fcos 0 1+constF (n+1) rho)*∏j:Fin n,(fcos j.succ (-3)+fcos 0 (-1))

lemma scalar_pair_delete (n:ℕ) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 3)=
      deletePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3)) := by
  exact scalarValue_fcos_delete 0 (-3) (fun j:Fin n =>fcos j.succ (-3))

lemma scalar_pair_delete_snoc {n:ℕ} (b:SpectralField (n+1)) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n 3) b)=
      deletePairScalar n*((b-fcos 0 (-9))*(b-fcos 0 9))*
        scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) b) := by
  have he:=scalarValue_fcos_delete (0:Fin (n+1)) (-3)
    (Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) b)
  unfold pairCosines
  rw [Fin.snoc_twoCons]
  norm_num only at he ⊢
  rw [he]
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last]
  dsimp only [deletePairScalar]
  ring

lemma scalar_pair_merge (n:ℕ) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 2)=
      mergePairScalar n*scalarValue (algebraMap ℂ (SpectralField (n+1)))
        (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) := by
  exact scalarValue_fcos_merge_all 0 (-1) Fin.succ (fun _:Fin n =>(-3))

lemma scalar_pair_merge_snoc {n:ℕ} (i:Fin (n+2)) (hi:i≠1) :
    scalarValue (algebraMap ℂ (SpectralField (n+1))) (Fin.snoc (pairCosines n 2) (pairBeta n 2 i))=
      mergePairScalar n*(pairBeta n 2 i+fcos 0 (-1))*
        scalarValue (algebraMap ℂ (SpectralField (n+1)))
          (Fin.snoc (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3))) (pairBeta n 2 i)) := by
  rw [pairBeta_of_ne i hi]
  have he:=scalarValue_fcos_merge_all (0:Fin (n+1)) (-1)
    (Fin.snoc Fin.succ (pairIndex n i)) (Fin.snoc (fun _:Fin n =>(-3:ℤ)) 3)
  have hf:(fun j =>fcos ((Fin.snoc Fin.succ (pairIndex n i) : Fin (n+1) → Fin (n+1)) j)
      ((Fin.snoc (fun _:Fin n =>(-3:ℤ)) 3 : Fin (n+1) → ℤ) j))=
      Fin.snoc (fun j:Fin n =>fcos j.succ (-3)) (deletionBeta (pairIndex n i)) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp only [Fin.snoc_last,deletionBeta_shiftedCosine]
    | cast j => simp only [Fin.snoc_castSucc]
  rw [hf] at he
  simp only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last] at he
  unfold pairCosines
  rw [Fin.snoc_twoCons]
  norm_num only at he ⊢
  rw [he]
  simp only [deletionBeta_shiftedCosine]
  dsimp only [mergePairScalar]
  rw [←Fin.cons_snoc_eq_snoc_cons]
  ring


 

 


lemma mergeMap_last {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) :
    LastMatrix (mergeMap (m:=m) r (show r+2≤n+2 by omega)) := by
  let j:Fin (n+1):=⟨r+1,by omega⟩
  change LastMatrix (localR (PartialColumn.rowPosition r hr).padTop (mergeWeights (constF m phase)) *
    functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j.castSucc)))
  exact (LastMatrix.local _ _).mul (LastMatrix.omit j)

lemma mergeMap_padTop {n m:ℕ} (r:ℕ) (hr:r+2≤n+1) (p:Pairing (n+1)) (q:Pairing n) :
    mergeMap (m:=m) r (show r+2≤n+2 by omega) p.padTop q.padTop=mergeMap r hr p q := by
  let j:Fin (n+1):=⟨r+1,by omega⟩
  calc
    _ = localR (PartialColumn.rowPosition r hr).padTop (mergeWeights (constF m phase)) p.padTop
        (q.padTop.map (Fin.succAboveOrderEmb j.castSucc)) := mul_functionMatrix _ _ _ _
    _ = localR (PartialColumn.rowPosition r hr) (mergeWeights (constF m phase)) p
        (q.map (Fin.succAboveOrderEmb j)) := by
      rw [←Pairing.omit_padTop,localR_padTop]
    _ = _ := (mul_functionMatrix _ _ _ _).symm

lemma deletionMap_last {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) :
    LastMatrix (deletionMap (m:=m) r (show r+2≤n+3 by omega)) := by
  let j:Fin (n+2):=⟨r+1,by omega⟩
  let k:Fin (n+1):=⟨r,by omega⟩
  change LastMatrix ((localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m))) *
    ((functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb j.castSucc))) *
      (functionMatrix (K:=SpectralField m) (Pairing.map (Fin.succAboveOrderEmb k.castSucc)))))
  exact (LastMatrix.local _ _).mul ((LastMatrix.omit j).mul (LastMatrix.omit k))

lemma deletionMap_padTop {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) (p:Pairing (n+2)) (q:Pairing n) :
    deletionMap (m:=m) r (show r+2≤n+3 by omega) p.padTop q.padTop=deletionMap r hr p q := by
  let j:Fin (n+2):=⟨r+1,by omega⟩
  let k:Fin (n+1):=⟨r,by omega⟩
  let B : Matrix (Pairing (n+3)) (Pairing (n+2)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb j.castSucc))
  let D : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb k.castSucc))
  let B' : Matrix (Pairing (n+2)) (Pairing (n+1)) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb j))
  let D' : Matrix (Pairing (n+1)) (Pairing n) (SpectralField m) :=
    functionMatrix (Pairing.map (Fin.succAboveOrderEmb k))
  change (localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m)) * (B*D)) p.padTop q.padTop =
    (localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m)) * (B'*D')) p q
  rw [←Matrix.mul_assoc,←Matrix.mul_assoc]
  dsimp only [B,D,B',D']
  rw [mul_functionMatrix,mul_functionMatrix,mul_functionMatrix,mul_functionMatrix]
  change localR (PartialColumn.rowPosition r hr).padTop (deletionWeights : Weights (SpectralField m)) p.padTop
    ((q.padTop.map (Fin.succAboveOrderEmb k.castSucc)).map (Fin.succAboveOrderEmb j.castSucc))=_
  rw [←Pairing.omit_padTop,←Pairing.omit_padTop,localR_padTop]

 

lemma LastDegree.mul_poly {K:Type*} [CommRing K] {n m d:ℕ}
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P)
    (F:Polynomial K) (hF:F.natDegree≤d) : LastDegree (m+d) (fun p =>F*P p) := by
  intro p k hk
  rw [Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have hk':ab.1+ab.2=k:=by simpa using hab
  by_cases ha:d<ab.1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hF ha),zero_mul]
  · rw [hP p ab.2 (by split_ifs at hk ⊢ <;> omega),mul_zero]

lemma LastDegree.mul_poly_top {K:Type*} [CommRing K] {n m d:ℕ}
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree m P)
    (F:Polynomial K) (hF:F.natDegree≤d) (p:Pairing n) :
    (F*P p.padTop).coeff (m+d)=F.coeff d*(P p.padTop).coeff m := by
  rw [add_comm,Polynomial.coeff_mul_add_eq_of_natDegree_le hF]
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk =>hP _ k (by simpa using hk))

end
end CriticalStrip.Diagram

end OAI
