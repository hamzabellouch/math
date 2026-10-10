import Mathlib
import OAI.Combinatorics.StripMass.NorthGluing
import OAI.Combinatorics.StripMass.SplitProjection

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

 

lemma twoVacancyInsertion_transpose_deletion {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    (twoVacancyInsertion (K:=SpectralField m) r hr).transpose * deletionMap (m:=m) r hr = 1 := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  let f := Fin.succAboveOrderEmb b
  let g := Fin.succAboveOrderEmb a
  have hab : f a = (PartialColumn.rowPosition r hr).left := by
    change b.succAbove a = _
    rw [Fin.succAbove_of_castSucc_lt _ _ (by change r<r+1; omega)]
    rfl
  have hf (p : Pairing n) : ¬((p.map g).map f).Occupied
      (PartialColumn.rowPosition r hr).right := (p.map g).map_not_occupied_omit b
  have hg (p : Pairing n) : ¬((p.map g).map f).Occupied
      (PartialColumn.rowPosition r hr).left := by
    rw [←hab, Pairing.map_occupied]
    exact p.map_not_occupied_omit a
  unfold twoVacancyInsertion deletionMap
  let F := functionMatrix (K:=SpectralField m) (Pairing.map f)
  let G := functionMatrix (K:=SpectralField m) (Pairing.map g)
  let E := functionMatrix (K:=SpectralField m) (Pairing.map f ∘ Pairing.map g)
  let L := localR (PartialColumn.rowPosition r hr) (deletionWeights : Weights (SpectralField m))
  have hfg : F*G=E := functionMatrix_mul _ _
  calc
    _ = E.transpose * (L*E) := congrArg (fun M => M.transpose*(L*M)) hfg
    _ = (E.transpose*L)*E := (Matrix.mul_assoc _ _ _).symm
    _ = 1 := by
      ext p q
      refine (mul_functionMatrix _ _ p q).trans ?_
      refine (transpose_functionMatrix_mul_apply _ _ p _).trans ?_
      change localR (PartialColumn.rowPosition r hr) deletionWeights ((p.map g).map f) ((q.map g).map f) =
        (if p=q then (1:SpectralField m) else 0)
      rw [localR_vacant_right _ _ _ _ (hf q) (hf p)]
      simp only [hg q,ite_false,
        (Pairing.map_injective f).eq_iff,(Pairing.map_injective g).eq_iff,eq_comm]

lemma deletionMap_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Function.Injective (deletionMap (m:=m) r hr).mulVec := by
  intro v w hvw
  have h := congrArg (twoVacancyInsertion (K:=SpectralField m) r hr).transpose.mulVec hvw
  rwa [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,
    twoVacancyInsertion_transpose_deletion,Matrix.one_mulVec,Matrix.one_mulVec] at h

 
def extendSource {K : Type*} [Zero K] {n : ℕ} (v : SourcePairing n → K) : Pairing (n+1) → K :=
  fun p => if h : p.Occupied (Fin.last n) then v ⟨p,h⟩ else 0

@[simp] lemma extendSource_apply {K : Type*} [Zero K] {n : ℕ}
    (v : SourcePairing n → K) (p : SourcePairing n) : extendSource v p.val=v p := by
  simp [extendSource,p.property]

lemma LastMatrix.mulVec_extendSource {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (v : SourcePairing n → K) :
    M.mulVec (extendSource v)=extendSource ((sourceBlock M).mulVec v) := by
  funext p
  by_cases hp : p.Occupied (Fin.last m)
  · rw [hM.source_mulVec _ ⟨p,hp⟩]
    simp only [extendSource_apply]
    rw [extendSource,dite_eq_left hp]
  · rw [extendSource,dite_eq_right hp]
    apply Finset.sum_eq_zero
    intro q _
    change M p q * extendSource v q=0
    by_cases hq : q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),zero_mul]
    · simp [extendSource,hq]

lemma LastMatrix.source_injective {K : Type*} [CommRing K] {n m : ℕ}
    {M : Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM : LastMatrix M)
    (h : Function.Injective M.mulVec) : Function.Injective (sourceBlock M).mulVec := by
  intro v w hvw
  have he := congrArg extendSource hvw
  rw [←hM.mulVec_extendSource,←hM.mulVec_extendSource] at he
  have hh := h he
  funext p
  simpa only [extendSource_apply] using congrFun hh p.val

lemma sourceBlock_merge_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    Function.Injective (sourceBlock (mergeMap (m:=m) r (show r+2≤n+2 by omega))).mulVec :=
  (mergeMap_last r hr).source_injective (mergeMap_injective r _)

lemma sourceBlock_deletion_injective {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    Function.Injective (sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega))).mulVec :=
  (deletionMap_last r hr).source_injective (deletionMap_injective r _)

lemma twoVacancyInsertion_last {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    LastMatrix (twoVacancyInsertion (K:=SpectralField m) r (show r+2≤n+3 by omega)) := by
  let b : Fin (n+2) := ⟨r+1,by omega⟩
  let a : Fin (n+1) := ⟨r,by omega⟩
  exact (LastMatrix.omit b).mul (LastMatrix.omit a)

lemma mergeProjection_last {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    LastMatrix (mergeProjection (m:=m) r (show r+2≤n+2 by omega)) := by
  let b : Fin (n+1) := ⟨r+1,by omega⟩
  exact (LastMatrix.omit b).transpose.mul
    (LastMatrix.local (PartialColumn.rowPosition r hr) _)

lemma deletionProjection_last {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    LastMatrix (deletionProjection (m:=m) r (show r+2≤n+3 by omega)) := by
  exact (twoVacancyInsertion_last r hr).transpose.mul
    (LastMatrix.local (PartialColumn.rowPosition r hr) _)

lemma sourceBlock_merge_factor {n m : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    sourceBlock (mergeMap (m:=m) r (show r+2≤n+2 by omega)) * sourceBlock (mergeProjection r (show r+2≤n+2 by omega)) =
      sourceBlock (localR (PartialColumn.rowPosition r hr).padTop (torusWeights (constF m phase^2))) := by
  refine ((mergeMap_last r hr).source_mul _).symm.trans ?_
  exact congrArg sourceBlock (mergeMap_mul_projection r _)

lemma sourceBlock_deletion_factor {n m : ℕ} (r : ℕ) (hr : r+2≤n+2) :
    sourceBlock (deletionMap (m:=m) r (show r+2≤n+3 by omega)) * sourceBlock (deletionProjection r (show r+2≤n+3 by omega)) =
      sourceBlock (localR (PartialColumn.rowPosition r hr).padTop (torusWeights (constF m phase^3))) := by
  refine ((deletionMap_last r hr).source_mul _).symm.trans ?_
  exact congrArg sourceBlock (deletionMap_mul_projection r _)

 

 


def twistedReflectionMonomial {n : ℕ} (k : Fin n → ℤ) :
    Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL (-e.toAdd) (∏ i, phase ^ (k i * e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (-(e.toAdd+f.toAdd)) (∏ i,phase^(k i*(e.toAdd i+f.toAdd i))) = _
    simp only [mul_add,zpow_add₀ phase_ne_zero,Finset.prod_mul_distrib,neg_add]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def twistedReflectLaurent {n : ℕ} (k : Fin n → ℤ) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (twistedReflectionMonomial k)).toRingHom

@[simp] lemma twistedReflectLaurent_monomial {n : ℕ} (k : Fin n → ℤ)
    (e : Fin n → ℤ) (z : ℂ) :
    twistedReflectLaurent k (monomialL e z) = monomialL (-e) (z * ∏ i,phase^(k i*e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (twistedReflectionMonomial k) (AddMonoidAlgebra.single e z) = _
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single (-e) _ = AddMonoidAlgebra.single (-e) _
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul]
  rfl

lemma twistedReflectLaurent_involutive {n : ℕ} (k : Fin n → ℤ) :
    Function.Involutive (twistedReflectLaurent k) := by
  have h : (twistedReflectLaurent k).comp (twistedReflectLaurent k) = RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change twistedReflectLaurent k (twistedReflectLaurent k (monomialL _ _)) = monomialL _ _
    all_goals rw [twistedReflectLaurent_monomial,twistedReflectLaurent_monomial]
    all_goals simp only [neg_neg,Pi.neg_apply,mul_neg,mul_assoc,←Finset.prod_mul_distrib,
      ←zpow_add₀ phase_ne_zero,add_neg_cancel,zpow_zero,Finset.prod_const_one,mul_one]
  exact fun f => DFunLike.congr_fun h f

def twistedReflectSpectral {n : ℕ} (k : Fin n → ℤ) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K:=SpectralField n)
    (g:=(algebraMap (SpectralRing n) (SpectralField n)).comp (twistedReflectLaurent k))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (twistedReflectLaurent_involutive k).injective)

@[simp] lemma twistedReflectSpectral_evalLaurent {n : ℕ} (k : Fin n → ℤ) (f : Laurent n) :
    twistedReflectSpectral k (evalLaurent f)=evalLaurent (twistedReflectLaurent k f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma twistedReflectSpectral_const {n : ℕ} (k : Fin n → ℤ) (z : ℂ) :
    twistedReflectSpectral k (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,twistedReflectSpectral_evalLaurent]
  change evalLaurent (twistedReflectLaurent k (monomialL 0 z)) = evalLaurent (monomialL 0 z)
  rw [twistedReflectLaurent_monomial]
  simp only [Pi.zero_apply,mul_zero,zpow_zero,Finset.prod_const_one,mul_one,neg_zero]

@[simp] lemma twistedReflectSpectral_variable {n : ℕ} (k : Fin n → ℤ) (i : Fin n) :
    twistedReflectSpectral k (variableF i)=constF n phase ^ k i / variableF i := by
  change twistedReflectSpectral k (evalLaurent (monomialL (variableExponent i) 1)) = _
  rw [twistedReflectSpectral_evalLaurent,twistedReflectLaurent_monomial]
  have he : (∏ j,phase^(k j * variableExponent i j))=phase^k i := by
    simp [variableExponent,Pi.single_apply]
  rw [he,one_mul,evalLaurent,map_monomialL_neg_variable]
  simp only [constF,map_zpow₀,div_eq_mul_inv]

lemma torusEvaluation_twistedReflect {n m : ℕ} (k : Fin n → ℤ)
    (z : Fin n → SpectralField m) (hz : ∀ i,z i≠0) (f : Laurent n) :
    torusEvaluation z hz (twistedReflectLaurent k f) =
      torusEvaluation (fun i => constF m phase^k i/z i)
        (fun i =>div_ne_zero (zpow_ne_zero _ (constF_phase_ne_zero m)) (hz i)) f := by
  have he : (torusEvaluation z hz).toRingHom.comp (twistedReflectLaurent k) =
      (torusEvaluation (fun i => constF m phase^k i/z i)
        (fun i =>div_ne_zero (zpow_ne_zero _ (constF_phase_ne_zero m)) (hz i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change torusEvaluation z hz (twistedReflectLaurent k (monomialL _ _)) =
      torusEvaluation _ _ (monomialL _ _)
    all_goals rw [twistedReflectLaurent_monomial]
    all_goals simp only [torusEvaluation_monomial,constF,map_mul,map_prod,map_zpow₀,
      Pi.neg_apply,zpow_neg,zpow_mul,div_eq_mul_inv,mul_zpow,inv_zpow,
      Finset.prod_mul_distrib,mul_assoc]
  exact DFunLike.congr_fun he f

lemma sum_zpow_eq_prod {K : Type*} [CommGroupWithZero K] {ι : Type*}
    (a : K) (ha : a≠0) (s : Finset ι) (v : ι → ℤ) :
    a^(∑ i∈s,v i) = ∏ i∈s,a^v i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi,Finset.prod_insert hi,zpow_add₀ ha,ih]

lemma reflectLaurent_eq_twisted (n : ℕ) : reflectLaurent n=twistedReflectLaurent (fun _:Fin n =>3) := by
  apply AddMonoidAlgebra.ringHom_ext <;> intro e
  all_goals change reflectLaurent n (monomialL _ _) = twistedReflectLaurent _ (monomialL _ _)
  all_goals rw [reflectLaurent_monomial,twistedReflectLaurent_monomial,
    Finset.mul_sum,sum_zpow_eq_prod phase phase_ne_zero]

lemma torusEvaluation_reflect {n m : ℕ} (z : Fin n → SpectralField m)
    (hz : ∀ i,z i≠0) (f : Laurent n) :
    torusEvaluation z hz (reflectLaurent n f) =
      torusEvaluation (fun i => constF m phase^3/z i)
        (fun i =>div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hz i)) f := by
  rw [reflectLaurent_eq_twisted,torusEvaluation_twistedReflect]
  rfl

 

def pairReflection (n s : ℕ) : SpectralField (n+1) →+* SpectralField (n+1) :=
  twistedReflectSpectral (Fin.cons (3-(s:ℤ)) (fun _ : Fin n =>3))

@[simp] lemma pairReflection_const (n s : ℕ) (z : ℂ) :
    pairReflection n s (constF (n+1) z)=constF (n+1) z := twistedReflectSpectral_const _ z

@[simp] lemma pairReflection_variable_zero (n s : ℕ) :
    pairReflection n s (variableF 0)=constF (n+1) phase^(3-(s:ℤ))/variableF 0 :=
  twistedReflectSpectral_variable _ _

@[simp] lemma pairReflection_variable_succ (n s : ℕ) (i : Fin n) :
    pairReflection n s (variableF i.succ)=constF (n+1) phase^3/variableF i.succ :=
  twistedReflectSpectral_variable _ _

lemma pairReflection_torusCos (n s : ℕ) (z : SpectralField (n+1)) :
    pairReflection n s (torusCos z)=torusCos (pairReflection n s z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

 

 


lemma pairReflection_pairPoint (n s : ℕ) (i : Fin (n+2)) :
    pairReflection n s (pairPoint n s i) =
      constF (n+1) phase^3 / pairPoint n s ((Equiv.swap 0 1) i) := by
  have hq := constF_phase_ne_zero (n+1)
  have hz := variableF_ne_zero (0:Fin (n+1))
  have hs : constF (n+1) phase ^ (3-(s:ℤ)) = constF (n+1) phase^3 / constF (n+1) phase^s := by
    rw [zpow_sub₀ hq]
    simp
  induction i using Fin.cases with
  | zero =>
    simp only [pairPoint,Fin.cons_zero,pairReflection_variable_zero,
      Equiv.swap_apply_left,Fin.cons_one,Fin.cons_zero]
    rw [hs]; field_simp
  | succ i => induction i using Fin.cases with
    | zero =>
      simp only [Fin.succ_zero_eq_one,pairPoint,Fin.cons_one,Fin.cons_zero,map_mul,map_pow,
        pairReflection_const,pairReflection_variable_zero,Equiv.swap_apply_right]
      rw [hs]; field_simp
    | succ i =>
      have h0 : i.succ.succ ≠ (0:Fin (n+2)) := Fin.succ_ne_zero _
      have h1 : i.succ.succ ≠ (1:Fin (n+2)) := by
        intro he
        have := congrArg Fin.val he
        simp only [Fin.val_succ,Fin.val_one] at this
        omega
      rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
      simp only [pairPoint,Fin.cons_succ,pairReflection_variable_succ]

lemma pairEvaluation_swap_reflect {n : ℕ} (s : ℕ) (f : Laurent (n+2)) :
    pairEvaluation n s (permLaurent (Equiv.swap 0 1) (reflectLaurent (n+2) f)) =
      pairReflection n s (pairEvaluation n s f) := by
  unfold pairEvaluation
  rw [torusEvaluation_permLaurent,torusEvaluation_reflect,
    torusEvaluation_fieldMap (pairReflection n s) (pairReflection_const n s)]
  congr 2
  funext i
  exact (pairReflection_pairPoint n s i).symm

lemma pairReflection_mergePoint (n : ℕ) (i : Fin (n+1)) :
    pairReflection n 2 (mergePoint n i) = constF (n+1) phase^3 / mergePoint n i := by
  induction i using Fin.cases with
  | zero =>
    simp only [mergePoint,Fin.cons_zero,map_mul,pairReflection_const,pairReflection_variable_zero]
    norm_num only
    field_simp [variableF_ne_zero,constF_phase_ne_zero]
  | succ i => simp only [mergePoint,Fin.cons_succ,deletePoint,pairReflection_variable_succ]

lemma pairReflection_mergeEvaluation {n : ℕ} (f : Laurent (n+1)) :
    pairReflection n 2 (mergeEvaluation n f) = mergeEvaluation n (reflectLaurent (n+1) f) := by
  unfold mergeEvaluation
  rw [torusEvaluation_fieldMap (pairReflection n 2) (pairReflection_const n 2),
    torusEvaluation_reflect]
  congr 2
  funext i
  exact pairReflection_mergePoint n i

lemma pairReflection_deleteEvaluation {n : ℕ} (f : Laurent n) :
    pairReflection n 3 (deleteEvaluation n f) = deleteEvaluation n (reflectLaurent n f) := by
  unfold deleteEvaluation
  refine (torusEvaluation_fieldMap (pairReflection n 3) (pairReflection_const n 3)
    (deletePoint n) (fun i => show deletePoint n i ≠ 0 from variableF_ne_zero i.succ) f).trans ?_
  refine Eq.trans ?_ (torusEvaluation_reflect (deletePoint n)
    (fun i => show deletePoint n i ≠ 0 from variableF_ne_zero i.succ) f).symm
  congr 2
  funext i
  exact pairReflection_variable_succ n 3 i

lemma twistedReflectSpectral_torusCos {n : ℕ} (k : Fin n → ℤ) (z : SpectralField n) :
    twistedReflectSpectral k (torusCos z) = torusCos (twistedReflectSpectral k z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

lemma twistedReflectSpectral_fcos {n : ℕ} (k : Fin n → ℤ) (i : Fin n) (r : ℤ) :
    twistedReflectSpectral k (fcos i r) = fcos i (-r-2*k i) := by
  rw [fcos_eq,twistedReflectSpectral_torusCos]
  simp only [map_mul,map_pow,twistedReflectSpectral_const,
    twistedReflectSpectral_variable]
  have hc (j:ℤ) : constF n (phase^j) = constF n phase^j := by simp [constF]
  have hq := constF_phase_ne_zero n
  have hp : constF n phase^(-r-2*k i) =
      (constF n phase^r * (constF n phase^k i)^2)⁻¹ := by
    rw [sub_eq_add_neg,zpow_add₀ hq,zpow_neg,zpow_neg,mul_comm (2:ℤ),zpow_mul]
    simp only [zpow_ofNat,mul_inv_rev]
    ring
  rw [fcos_eq]
  simp only [hc]
  calc
    torusCos (constF n phase^r * (constF n phase^k i / variableF i)^2) =
        torusCos ((constF n phase^(-r-2*k i)*variableF i^2)⁻¹) := by
      congr 1
      rw [hp]
      field_simp
    _ = _ := torusCos_inv _

lemma pairReflection_fcos_zero (n s : ℕ) (r : ℤ) :
    pairReflection n s (fcos 0 r) = fcos 0 (-r-2*(3-(s:ℤ))) := by
  exact twistedReflectSpectral_fcos _ _ _

lemma pairReflection_fcos_succ (n s : ℕ) (i : Fin n) (r : ℤ) :
    pairReflection n s (fcos i.succ r) = fcos i.succ (-r-6) := by
  exact twistedReflectSpectral_fcos _ _ _

lemma pairReflection_mergeScalar (n : ℕ) :
    pairReflection n 2 (mergePairScalar n) = mergePairScalar n := by
  unfold mergePairScalar
  simp only [map_mul,map_add,map_prod,pairReflection_fcos_zero,pairReflection_fcos_succ,
    pairReflection_const]
  norm_num only
  ring

lemma pairReflection_deleteScalar (n : ℕ) :
    pairReflection n 3 (deletePairScalar n) = deletePairScalar n := by
  unfold deletePairScalar
  simp only [map_mul,map_add,map_sub,map_prod,pairReflection_fcos_zero,pairReflection_fcos_succ,
    pairReflection_const]
  norm_num only
  have hp : (∏ j:Fin n, (fcos j.succ (-3)-fcos 0 9)*(fcos j.succ (-3)-fcos 0 (-9))) =
      ∏ j:Fin n, (fcos j.succ (-3)-fcos 0 (-9))*(fcos j.succ (-3)-fcos 0 9) := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hp]
  ring

 

 


lemma constF_C_ne_zero (n : ℕ) : constF n C≠0 := by
  simpa only [constF,map_ne_zero,Complex.ofReal_ne_zero] using C_ne_zero

lemma torusL_split_nonzero (n s : ℕ) (hs : s=2 ∨ s=3) :
    torusL (constF n phase^s) ≠ 0 := by
  rcases hs with rfl | rfl
  · rw [torusL_phase_two]; exact constF_C_ne_zero n
  · rw [torusL_phase_three]
    simpa only [←torusL_one] using torusL_one_ne_zero n

 

lemma polynomialNorthSource_reflected_pair (n s : ℕ) (hs : s=2 ∨ s=3) :
    (fun p : SourcePairing (n+2) => pairReflection n s
      (pairEvaluation n s (polynomialNorthSource (n+2) p))) =
    (sourceBlock (localR (PartialColumn.rowPosition 0 (show 2≤n+2 by omega)).padTop
      (torusWeights (constF (n+1) phase^s)))).mulVec
      (fun p => pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) := by
  let φ := pairEvaluation n s
  let a := (PartialColumn.rowPosition 0 (show 2≤n+2 by omega)).padTop
  let x := variableF (1:Fin (n+2)) / variableF 0
  let y := constF (n+1) phase^s
  have hx : RationalAt φ.toRingHom x y := by
    have hh := (rationalAt_pair_variable (n:=n) s (1:Fin (n+2))).div
      (rationalAt_pair_variable s 0) (variableF_ne_zero 0)
    simpa only [pairPoint,Fin.cons_one,Fin.cons_zero,mul_div_cancel_right₀ _ (variableF_ne_zero 0)] using hh
  have hy : y≠0 := pow_ne_zero _ (constF_phase_ne_zero _)
  have hw : ∀ t, RationalAt φ.toRingHom ((torusWeights x).tile t) ((torusWeights y).tile t) :=
    rationalAt_torusWeights φ hx hy (torusL_split_nonzero (n+1) s hs)
  have hv (p : SourcePairing (n+2)) : RationalAt φ.toRingHom
      (reflectSpectral (n+2) (evalLaurent (polynomialNorthSource (n+2) p)))
      (pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) := by
    rw [reflectSpectral_evalLaurent]
    exact RationalAt.algebraMap _
  funext p
  have hright := RationalAt.mulVec (φ:=φ.toRingHom)
    (sourceBlock (localR a (torusWeights x))) (sourceBlock (localR a (torusWeights y)))
    (fun q => reflectSpectral (n+2) (evalLaurent (polynomialNorthSource (n+2) q)))
    (fun q => pairEvaluation n s (reflectLaurent (n+2) (polynomialNorthSource (n+2) q)))
    (fun q q' => rationalAt_localR φ a (torusWeights x) (torusWeights y) hw q.val q'.val) hv p
  have he := congrFun (polynomialNorthSource_reflected_covariance 0 (show 2≤n+2 by omega)) p
  change permSpectral (Equiv.swap 0 1) (reflectSpectral (n+2)
    (evalLaurent (polynomialNorthSource (n+2) p))) =
    (sourceBlock (localR a (torusWeights x))).mulVec _ p at he
  rw [←he,reflectSpectral_evalLaurent,permSpectral_evalLaurent] at hright
  have hleft := RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+2))
    (permLaurent (Equiv.swap 0 1) (reflectLaurent (n+2) (polynomialNorthSource (n+2) p)))
  have hh := hleft.unique hright
  change pairEvaluation n s _ = _ at hh
  rw [pairEvaluation_swap_reflect] at hh
  exact hh

lemma pairReflection_mergeMap {n m s : ℕ} (r : ℕ) (hr : r+2≤n+1) :
    (mergeMap (m:=m+1) r hr).map (pairReflection m s)=mergeMap r hr := by
  simp only [mergeMap]
  let E := functionMatrix (K:=SpectralField (m+1))
    (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+1))))
  let S := localR (PartialColumn.rowPosition r hr) (mergeWeights (constF (m+1) phase))
  have hw : (mergeWeights (constF (m+1) phase)).map (pairReflection m s) =
      mergeWeights (constF (m+1) phase) := by
    simp [Weights.map,mergeWeights,map_div₀]
  calc
    _ = S.map (pairReflection m s) * E.map (pairReflection m s) := Matrix.map_mul
    _ = _ := by
      dsimp only [S,E]
      rw [localR_map_hom,functionMatrix_map_hom,hw]
      rfl

 

theorem polynomialNorthSource_reflected_merge (n : ℕ) :
    (sourceBlock (mergeProjection (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
      (fun p => pairEvaluation n 2 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) =
      mergePairScalar n •
        (fun q => mergeEvaluation n (reflectLaurent (n+1) (polynomialNorthSource (n+1) q))) := by
  have ht : (fun p : SourcePairing (n+2) => pairReflection n 2
      (pairEvaluation n 2 (polynomialNorthSource (n+2) p))) =
      mergePairScalar n •
        (sourceBlock (mergeMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => mergeEvaluation n (reflectLaurent (n+1) (polynomialNorthSource (n+1) q))) := by
    funext p
    rw [polynomialNorthSource_merge,map_mul,pairReflection_mergeScalar,
      RingHom.map_mulVec,sourceBlock_map,pairReflection_mergeMap]
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 2
    funext q
    exact pairReflection_mergeEvaluation _
  have hc := polynomialNorthSource_reflected_pair n 2 (Or.inl rfl)
  apply sourceBlock_merge_injective (n:=n+1) (m:=n+1) 0 (show 2≤n+2 by omega)
  rw [Matrix.mulVec_mulVec]
  refine (congrArg (fun M => M.mulVec (fun p =>
    pairEvaluation n 2 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))))
      (sourceBlock_merge_factor (m:=n+1) 0 (show 2≤n+1+1 by omega))).trans ?_
  rw [←hc,ht,Matrix.mulVec_smul]

 
theorem polynomialNorthSource_reflected_delete (n : ℕ) :
    (sourceBlock (deletionProjection (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
      (fun p => pairEvaluation n 3 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))) =
      deletePairScalar n •
        (fun q => deleteEvaluation n (reflectLaurent n (polynomialNorthSource n q))) := by
  have ht : (fun p : SourcePairing (n+2) => pairReflection n 3
      (pairEvaluation n 3 (polynomialNorthSource (n+2) p))) =
      deletePairScalar n •
        (sourceBlock (deletionMap (m:=n+1) 0 (show 2≤n+3 by omega))).mulVec
          (fun q => deleteEvaluation n (reflectLaurent n (polynomialNorthSource n q))) := by
    funext p
    rw [polynomialNorthSource_delete,map_mul,pairReflection_deleteScalar,
      RingHom.map_mulVec,sourceBlock_map,deletionMap_map]
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 2
    funext q
    exact pairReflection_deleteEvaluation _
  have hc := polynomialNorthSource_reflected_pair n 3 (Or.inr rfl)
  apply sourceBlock_deletion_injective (n:=n) (m:=n+1) 0 (show 2≤n+2 by omega)
  rw [Matrix.mulVec_mulVec]
  refine (congrArg (fun M => M.mulVec (fun p =>
    pairEvaluation n 3 (reflectLaurent (n+2) (polynomialNorthSource (n+2) p))))
      (sourceBlock_deletion_factor (m:=n+1) 0 (show 2≤n+2 by omega))).trans ?_
  rw [←hc,ht,Matrix.mulVec_smul]

end
end CriticalStrip.Diagram

end OAI
