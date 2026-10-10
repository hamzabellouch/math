import Mathlib
import OAI.Combinatorics.StripMass.NodalScalarDeletion

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma evalLaurent_monomial_scale {n : ℕ} (e : Fin n → ℤ) (c z : ℂ) :
    (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (c*z))=constF n c*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z) := by
  rw [←map_constantL]
  change (algebraMap (SpectralRing n) (SpectralField n)) (monomialL e (c*z))=(algebraMap (SpectralRing n) (SpectralField n)) (monomialL 0 c)*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)
  rw [←map_mul,monomialL_mul,zero_add]

lemma evalLaurent_monomial_quot {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) (c : ℂ) :
    (algebraMap (SpectralRing n) (SpectralField n)) (monomialL (-e) (c/z))=constF n c/(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z) := by
  rw [div_eq_mul_inv,div_eq_mul_inv,evalLaurent_monomial_scale]
  congr 1
  exact (map_monomialL_inv e z hz).symm

 
def torusNumeratorL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Tile → Laurent n
  | .vacant => sineL e (phase^2*z)*sineL e (phase^3*z)
  | .vertical₀ | .vertical₁ => constantL n d*sineL (-e) (phase^3/z)
  | .cap | .cup => constantL n d*sineL e z
  | .diagonal₀ | .diagonal₁ => sineL e z*sineL (-e) (phase^3/z)
  | .verticalPair => sineL (-e) (phase^3/z)*sineL (-e) (phase^2/z)
  | .capCup => sineL e (z/phase)*sineL e z

lemma sineL_map_scale {n : ℕ} (e : Fin n → ℤ) (c z : ℂ) (hc:c≠0) (hz:z≠0) :
    (algebraMap (SpectralRing n) (SpectralField n)) (sineL e (c*z))=torusSin (constF n c*(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) := by
  rw [sineL_map e (c*z) (mul_ne_zero hc hz),evalLaurent_monomial_scale]

lemma sineL_map_quot {n : ℕ} (e : Fin n → ℤ) (z c : ℂ) (hc:c≠0) (hz:z≠0) :
    (algebraMap (SpectralRing n) (SpectralField n)) (sineL (-e) (c/z))=torusSin (constF n c/(algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) := by
  rw [sineL_map _ _ (div_ne_zero hc hz),evalLaurent_monomial_quot e z hz]

lemma torusNumeratorL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz:z≠0) (t : Tile) :
    (algebraMap (SpectralRing n) (SpectralField n)) (torusNumeratorL e z t)=torusNumerator ((algebraMap (SpectralRing n) (SpectralField n)) (monomialL e z)) t := by
  cases t
  all_goals simp only [torusNumeratorL,torusNumerator,torusL,map_mul,map_constantL]
  all_goals try rw [sineL_map e z hz]
  all_goals try rw [sineL_map_scale e (phase^2) z (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_scale e (phase^3) z (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_quot e z (phase^3) (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try rw [sineL_map_quot e z (phase^2) (pow_ne_zero _ phase_ne_zero) hz]
  all_goals try simp only [constF,map_pow]
  have he:z/phase=phase⁻¹*z := by ring
  rw [he,sineL_map_scale e phase⁻¹ z (inv_ne_zero phase_ne_zero) hz]
  simp only [constF,map_inv₀]
  congr 2
  exact inv_mul_eq_div _ _

lemma sineL_product_box {n : ℕ} (e f : Fin n → ℤ) (z w : ℂ) (b : Fin n → ℕ)
    (he : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) (hf : ∀ i,-(b i:ℤ)≤f i ∧ f i≤b i) :
    LaurentBox (sineL e z*sineL f w) (b+b) :=
  LaurentBox.mul (LaurentBox.sine e z b he) (LaurentBox.sine f w b hf)

lemma constant_sineL_box {n : ℕ} (e : Fin n → ℤ) (z w : ℂ) (b : Fin n → ℕ)
    (he : ∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) :
    LaurentBox (constantL n z*sineL e w) (b+b) :=
  LaurentBox.mul ((LaurentBox.constant z).mono (fun i => Nat.zero_le (b i)))
    (LaurentBox.sine e w b he)

lemma torusNumeratorL_box {n : ℕ} (e : Fin n → ℤ) (z : ℂ)
    (b : Fin n → ℕ) (h:∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) (t : Tile) :
    LaurentBox (torusNumeratorL e z t) (b+b) := by
  have hn : ∀ i,-(b i:ℤ)≤(-e) i ∧ (-e) i≤b i := by
    intro i; have := h i; simp only [Pi.neg_apply]; omega
  cases t with
  | vacant => exact sineL_product_box e e _ _ b h h
  | cap => exact constant_sineL_box e _ _ b h
  | cup => exact constant_sineL_box e _ _ b h
  | vertical₀ => exact constant_sineL_box (-e) _ _ b hn
  | vertical₁ => exact constant_sineL_box (-e) _ _ b hn
  | diagonal₀ => exact sineL_product_box e (-e) _ _ b h hn
  | diagonal₁ => exact sineL_product_box e (-e) _ _ b h hn
  | verticalPair => exact sineL_product_box (-e) (-e) _ _ b hn hn
  | capCup => exact sineL_product_box e e _ _ b h h


 

 


lemma rawLocal_map {K L : Type*} [CommRing K] [CommRing L] (f : K →+* L)
    {n : ℕ} (r : Position n) (w : Tile → K) :
    (rawLocal r w).map f=rawLocal r (fun t => f (w t)) := by
  ext p q
  simp only [rawLocal,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,
    smul_eq_mul,map_sum,map_mul]
  apply Finset.sum_congr rfl
  intro t _
  unfold optionMatrix
  split_ifs <;> simp

def LaurentMatrixBox {n : ℕ} {α β : Type*} (A : Matrix α β (Laurent n)) (b : Fin n → ℕ) : Prop :=
  ∀ p q,LaurentBox (A p q) b

lemma LaurentMatrixBox.one {n : ℕ} {α : Type*} [DecidableEq α] :
    LaurentMatrixBox (1:Matrix α α (Laurent n)) 0 := by
  intro p q
  by_cases h:p=q
  · subst p; simp only [Matrix.one_apply_eq]; exact LaurentBox.one
  · simp only [Matrix.one_apply_ne h]; exact LaurentBox.zero _

lemma LaurentMatrixBox.mul {n : ℕ} {α β γ : Type*} [Fintype β]
    {A : Matrix α β (Laurent n)} {B : Matrix β γ (Laurent n)}
    {a b : Fin n → ℕ} (hA : LaurentMatrixBox A a) (hB : LaurentMatrixBox B b) :
    LaurentMatrixBox (A*B) (a+b) := by
  intro p q
  rw [Matrix.mul_apply]
  exact LaurentBox.sum _ _ _ (fun i _ => (hA p i).mul (hB i q))

lemma LaurentMatrixBox.smul {n : ℕ} {α β : Type*} {A : Matrix α β (Laurent n)}
    {c : Laurent n} {a b : Fin n → ℕ} (hc : LaurentBox c a) (hA : LaurentMatrixBox A b) :
    LaurentMatrixBox (c • A) (a+b) := by
  intro p q
  exact hc.mul (hA p q)

lemma rawLocal_box {n m : ℕ} (r : Position m) (w : Tile → Laurent n)
    (b : Fin n → ℕ) (hw : ∀ t,LaurentBox (w t) b) :
    LaurentMatrixBox (rawLocal r w) b := by
  intro p q
  simp only [rawLocal,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply LaurentBox.sum
  intro t _
  unfold optionMatrix
  split_ifs
  · simpa using hw t
  · simp only [mul_zero]; exact LaurentBox.zero _

lemma matrixPrefix_box_partial {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Fin m → Matrix α α (Laurent n)) (b : Fin m → Fin n → ℕ)
    (hA : ∀ i,LaurentMatrixBox (A i) (b i)) (k : ℕ) :
    LaurentMatrixBox (matrixPrefix A k)
      (∑ j ∈ Finset.range k, (if h : j < m then b ⟨j, h⟩ else 0)) := by
  induction k with
  | zero => simp only [matrixPrefix,Finset.range_zero,Finset.sum_empty]; exact LaurentMatrixBox.one
  | succ k ih =>
    rw [matrixPrefix,Finset.sum_range_succ]
    by_cases hk : k < m
    · rw [dite_eq_left hk,dite_eq_left hk,add_comm]
      exact (hA ⟨k,hk⟩).mul ih
    · rw [dite_eq_right hk,dite_eq_right hk,add_zero]
      exact ih

lemma matrixPrefix_box {n m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (A : Fin m → Matrix α α (Laurent n)) (b : Fin m → Fin n → ℕ)
    (hA : ∀ i,LaurentMatrixBox (A i) (b i)) :
    LaurentMatrixBox (matrixPrefix A m) (∑ j,b j) := by
  rw [Finset.sum_fin_eq_sum_range]
  exact matrixPrefix_box_partial A b hA m


 

 


lemma map_monomialL_add_variable {n : ℕ} (i j : Fin n) (z : ℂ) :
    evalLaurent (monomialL (variableExponent i+variableExponent j) z)=
      constF n z*(variableF i*variableF j) := by
  have hm : monomialL (variableExponent i+variableExponent j) z =
      monomialL (variableExponent i) z*monomialL (variableExponent j) 1 := by simp
  rw [hm,evalLaurent,map_mul,map_monomialL_variable,map_monomialL_variable]
  simp only [constF,map_one,one_mul,mul_assoc]

 

def reducedMovingStepL {n : ℕ} (i j : Fin n) :
    Matrix (Pairing (n+1)) (Pairing (n+1)) (Laurent n) :=
  if j=i then 1 else
    (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ))) •
      if i<j then rawLocal (PartialColumn.rowPosition j.val (by omega))
        (torusNumeratorL (variableExponent i-variableExponent j) (phase^3))
      else torusNumeratorL (variableExponent i-variableExponent j) (phase^3) .vacant • 1

lemma reducedMovingStepL_scalar {n : ℕ} (i j : Fin n) :
    evalLaurent (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ)))=
      -4*torusSin (variableF i*variableF j/constF n phase^6) := by
  rw [evalLaurent,map_mul,map_constantL,sineL_map _ _ (zpow_ne_zero _ phase_ne_zero)]
  change constF n (-4)*torusSin (evalLaurent (monomialL _ _))=_
  rw [map_monomialL_add_variable]
  simp only [constF,map_neg,map_ofNat,map_zpow₀,zpow_neg,map_inv₀]
  congr 2
  field_simp

lemma torusNumeratorL_pair_map {n : ℕ} (i j : Fin n) (t : Tile) :
    evalLaurent (torusNumeratorL (variableExponent i-variableExponent j) (phase^3) t)=
      torusNumerator (constF n phase^3*(variableF i/variableF j)) t := by
  change (algebraMap (SpectralRing n) (SpectralField n)) (_)=_
  rw [torusNumeratorL_map _ _ (pow_ne_zero _ phase_ne_zero)]
  change torusNumerator (evalLaurent (monomialL _ _)) t=_
  rw [map_monomialL_sub_variable]
  simp only [constF,map_pow]

lemma matrix_map_ring_smul {K L α β : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (c : K) (A : Matrix α β K) :
    (c • A).map f=f c • A.map f := by
  ext i j
  exact f.map_mul c (A i j)

lemma reducedMovingStepL_map {n : ℕ} (i j : Fin n) :
    (reducedMovingStepL i j).map (algebraMap (SpectralRing n) (SpectralField n))=
      reducedMovingStep i j := by
  by_cases h:j=i
  · simp [reducedMovingStepL,reducedMovingStep,h]
  · simp only [reducedMovingStepL,reducedMovingStep,ite_eq_right h]
    rw [matrix_map_ring_smul]
    change evalLaurent _ • _ = _
    rw [reducedMovingStepL_scalar]
    congr 1
    by_cases hij:i<j
    · rw [ite_eq_left hij,ite_eq_left hij,rawLocal_map]
      congr 1
      funext t
      exact torusNumeratorL_pair_map i j t
    · rw [ite_eq_right hij,ite_eq_right hij,matrix_map_ring_smul]
      rw [show (1 : Matrix (Pairing (n+1)) (Pairing (n+1)) (Laurent n)).map
        (algebraMap (SpectralRing n) (SpectralField n))=1 by simp]
      congr 1
      exact torusNumeratorL_pair_map i j .vacant

lemma reducedMovingTrainL_map {n : ℕ} (i : Fin n) :
    (matrixPrefix (reducedMovingStepL i) n).map (algebraMap (SpectralRing n) (SpectralField n))=
      matrixPrefix (reducedMovingStep i) n := by
  rw [matrixPrefix_map]
  congr 1
  funext j
  exact reducedMovingStepL_map i j


 

 


 

def interpolationNumerator {R : Type*} [CommRing R] {n : ℕ}
    (b y : Fin n → R) (k : Fin n) : R :=
  ((Matrix.vandermonde b).updateCol k y).det

lemma vandermonde_mulVec_coeff {R : Type*} [CommRing R] {n : ℕ}
    (b : Fin n → R) (p : Polynomial R) (hp:p.degree<n) :
    (Matrix.vandermonde b).mulVec (fun k : Fin n => p.coeff k)=fun i => p.eval (b i) := by
  funext i
  simp only [Matrix.mulVec,dotProduct,Matrix.vandermonde_apply]
  rw [show (∑ x : Fin n, b i ^ (x:ℕ) * p.coeff (x:ℕ)) =
    ∑ x ∈ Finset.range n, b i ^ x * p.coeff x from
    Fin.sum_univ_eq_sum_range (fun x => b i ^ x * p.coeff x) n]
  by_cases hz:p=0
  · simp [hz]
  · rw [Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt hz).mpr hp)]
    apply Finset.sum_congr rfl
    intro k _
    exact mul_comm _ _

lemma interpolationNumerator_eq_det_mul_coeff {K : Type*} [Field K] {n : ℕ}
    (b y : Fin n → K) (hb:Function.Injective b) (k : Fin n) :
    interpolationNumerator b y k=(Matrix.vandermonde b).det*
      (Lagrange.interpolate Finset.univ b y).coeff k := by
  let p:=Lagrange.interpolate Finset.univ b y
  have hp:p.degree<n := by
    simpa only [Finset.card_univ,Fintype.card_fin] using Lagrange.degree_interpolate_lt (s:=Finset.univ) y hb.injOn
  have hev : (Matrix.vandermonde b).mulVec (fun k : Fin n => p.coeff k)=y := by
    rw [vandermonde_mulVec_coeff b p hp]
    funext i
    exact Lagrange.eval_interpolate_at_node y hb.injOn (Finset.mem_univ i)
  have h:=congrArg (Matrix.mulVec (Matrix.vandermonde b).adjugate) hev
  rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec,
    ←Matrix.cramer_eq_adjugate_mulVec] at h
  exact (congrFun h k).symm

lemma interpolationNumerator_map {R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) {n : ℕ} (b y : Fin n → R) (k : Fin n) :
    f (interpolationNumerator b y k)=interpolationNumerator (fun i => f (b i)) (fun i => f (y i)) k := by
  unfold interpolationNumerator
  rw [RingHom.map_det]
  congr 1
  change ((Matrix.vandermonde b).updateCol k y).map f = _
  ext i j
  simp only [Matrix.map_apply,Matrix.updateCol_apply,Matrix.vandermonde_apply]
  split_ifs <;> simp only [map_pow]

lemma interpolationNumerator_collision {R : Type*} [CommRing R] {n : ℕ}
    (b y : Fin n → R) (i j : Fin n) (hij:i≠j) (hb:b i=b j) (hy:y i=y j) (k : Fin n) :
    interpolationNumerator b y k=0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext a
  simp only [Matrix.updateCol_apply,Matrix.vandermonde_apply]
  split_ifs <;> simp only [hb,hy]


 

 


lemma functionMatrix_ring_map {R S P Q : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (v : P → Q) : (functionMatrix (K:=R) v).map f=functionMatrix v := by
  ext p q
  simp only [Matrix.map_apply,functionMatrix,optionMatrix]
  split_ifs <;> simp

def deletionMapL {n m : ℕ} (r : ℕ) (hr:r+2≤n+2) :
    Matrix (Pairing (n+2)) (Pairing n) (Laurent m) :=
  @HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (rawLocal (PartialColumn.rowPosition r hr) (deletionWeights : Weights (Laurent m)).tile)
    (@HMul.hMul _ _ _ Matrix.instHMulOfFintypeOfMulOfAddCommMonoid (functionMatrix (K:=Laurent m) (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2)))))
      (functionMatrix (K:=Laurent m) (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))))

lemma deletionMapL_map {n m : ℕ} (r : ℕ) (hr:r+2≤n+2) :
    (deletionMapL (m:=m) r hr).map (algebraMap (SpectralRing m) (SpectralField m))=deletionMap r hr := by
  unfold deletionMapL
  rw [Matrix.map_mul,Matrix.map_mul,functionMatrix_ring_map,functionMatrix_ring_map,rawLocal_map]
  unfold deletionMap
  congr 2
  funext t
  cases t <;> simp [Weights.tile,deletionWeights]

def nodalHeadL {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] : Laurent n :=
  if occupied then constantL n (4*c)*sineL (-variableExponent i) (phase^3)
  else cosineL ((2:ℤ) • variableExponent i) (phase^(-3:ℤ))+
    cosineL ((2:ℤ) • variableExponent i) (phase^3)+constantL n rho

lemma nodalHeadL_map {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] :
    evalLaurent (nodalHeadL i occupied)=reducedNodalHead i occupied := by
  by_cases h:occupied
  · simp only [nodalHeadL,reducedNodalHead,ite_eq_left h,evalLaurent,map_mul,map_constantL]
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero),map_monomialL_neg_variable]
    change constF n 4*constF n c*torusSin (constF n (phase^3)*(variableF i)⁻¹)=_
    simp only [constF,map_ofNat,map_pow,div_eq_mul_inv]
  · simp only [nodalHeadL,reducedNodalHead,ite_eq_right h,evalLaurent,map_add,map_constantL]
    change evalLaurent (cosineL _ _)+evalLaurent (cosineL _ _)+constF n rho=_
    rw [←deletionBeta_laurent]
    congr 2
    rw [cosineL_map _ _ (zpow_ne_zero _ phase_ne_zero),map_monomialL_two_variable]
    change torusCos (constF n (phase^(-3:ℤ))*variableF i^2)=torusCos (variableF i^2/constF n phase^3)
    congr 1
    simp only [constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow]
    ring

def reflectionFactorL {n : ℕ} (i j : Fin n) : Laurent n :=
  if j=i then 1 else sineL (variableExponent i+variableExponent j) (phase^3)

lemma reflectionFactorL_map {n : ℕ} (i j : Fin n) :
    evalLaurent (reflectionFactorL i j)=reflectionFactor i j := by
  by_cases h:j=i
  · simp [reflectionFactorL,reflectionFactor,h,evalLaurent]
  · simp only [reflectionFactorL,reflectionFactor,ite_eq_right h]
    change (algebraMap (SpectralRing n) (SpectralField n)) (sineL _ _)=_
    rw [sineL_map _ _ (pow_ne_zero _ phase_ne_zero)]
    change torusSin (evalLaurent (monomialL _ _))=_
    rw [map_monomialL_add_variable]
    simp only [constF,map_pow]

 

def nodalDatumL {n : ℕ} (W : Pairing n → Laurent n) (i : Fin (n+1)) (p : Pairing (n+2)) : Laurent (n+1) :=
  (∏ j,reflectionFactorL i j)*nodalHeadL i (p.Occupied (Fin.last (n+1)))*
    (matrixPrefix (reducedMovingStepL i) (n+1)).mulVec
      ((deletionMapL i.val (show i.val+2≤n+2 by omega)).mulVec
        (fun q => insertLaurent i (W q))) p

lemma nodalDatumL_map {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (p : Pairing (n+2)) :
    evalLaurent (nodalDatumL W i p)=
      nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := by
  rw [reducedNodalDatum_eq]
  simp only [nodalDatumL,evalLaurent,map_mul,map_prod]
  change (∏ j,evalLaurent (reflectionFactorL i j))*evalLaurent (nodalHeadL i _) *
    (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      ((matrixPrefix (reducedMovingStepL i) (n+1)).mulVec _ p)=_
  simp only [reflectionFactorL_map,nodalHeadL_map]
  simp only [RingHom.map_mulVec,Function.comp_def,reducedMovingTrainL_map,deletionMapL_map]
  have hw (q:Pairing n) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (insertLaurent i (W q))=insertSpectral i (rationalVacuum n q) := by
    change evalLaurent (insertLaurent i (W q))=_
    rw [←insertSpectral_evalLaurent,hW]
  simp only [hw]
  exact mul_assoc _ _ _


 

 


lemma LaurentBox.cosine {n : ℕ} (e:Fin n → ℤ) (z:ℂ) (b:Fin n → ℕ)
    (he:∀ i,-(b i:ℤ)≤e i ∧ e i≤b i) : LaurentBox (cosineL e z) b := by
  apply LaurentBox.add
  · exact LaurentBox.single e _ b he
  · exact LaurentBox.single (-e) _ b (by intro i; have :=he i; simp only [Pi.neg_apply]; omega)

lemma LaurentBox.pow {n : ℕ} {f:Laurent n} {b:Fin n → ℕ} (hf:LaurentBox f b) (k:ℕ) :
    LaurentBox (f^k) (fun i => k*b i) := by
  induction k with
  | zero =>
    rw [pow_zero]
    intro e he i
    simpa only [Nat.zero_mul,Pi.zero_apply] using LaurentBox.one e he i
  | succ k ih =>
    rw [pow_succ]
    convert ih.mul hf using 1
    funext i
    simp [Nat.succ_mul]

lemma LaurentBox.insert {n : ℕ} (i:Fin (n+1)) {f:Laurent n} {b:Fin n → ℕ}
    (hf:LaurentBox f b) : LaurentBox (insertLaurent i f) (Fin.insertNth i 0 b) := by
  intro e he k
  have hs : e∈f.coeff.support.image (insertExponent i) :=
    (Finsupp.mapDomain_support (s:=f.coeff) (f:=insertExponent i)) (Finsupp.mem_support_iff.mpr he)
  obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hs
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · simp [insertExponent]
  · simpa only [insertExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Fin.insertNth_apply_succAbove] using
      hf a (Finsupp.mem_support_iff.mp ha) j

lemma LaurentMatrixBox.mulVec {n:ℕ} {α β:Type*} [Fintype β]
    {A:Matrix α β (Laurent n)} {v:β → Laurent n} {a b:Fin n → ℕ}
    (hA:LaurentMatrixBox A a) (hv:∀ q,LaurentBox (v q) b) :
    ∀ p,LaurentBox (A.mulVec v p) (a+b) := by
  intro p
  exact LaurentBox.sum _ _ _ (fun q _ => (hA p q).mul (hv q))

lemma functionMatrix_box {n:ℕ} {α β:Type*} (f:α → β) :
    LaurentMatrixBox (functionMatrix (K:=Laurent n) f) 0 := by
  intro p q
  unfold functionMatrix optionMatrix
  split_ifs
  · exact LaurentBox.one
  · exact LaurentBox.zero _

lemma LaurentMatrixBox.mono {n:ℕ} {α β:Type*} {A:Matrix α β (Laurent n)} {a b:Fin n → ℕ}
    (hA:LaurentMatrixBox A a) (hab:∀ i,a i≤b i) : LaurentMatrixBox A b :=
  fun p q => (hA p q).mono hab


 

 


def pairBound {n:ℕ} (i j k:Fin n) : ℕ := if j=i then 0 else if k=i ∨ k=j then 1 else 0

def selfBound {n:ℕ} (i:Fin n) (b:ℕ) (k:Fin n) : ℕ := if k=i then b else 0

lemma pairBound_add {n:ℕ} (i j:Fin n) (h:j≠i) (k:Fin n) :
    -(pairBound i j k:ℤ)≤(variableExponent i+variableExponent j) k ∧
      (variableExponent i+variableExponent j) k ≤ pairBound i j k := by
  by_cases hki:k=i <;> by_cases hkj:k=j
  all_goals simp_all [pairBound,variableExponent]

lemma pairBound_sub {n:ℕ} (i j k:Fin n) :
    -(pairBound i j k:ℤ)≤(variableExponent i-variableExponent j) k ∧
      (variableExponent i-variableExponent j) k ≤ pairBound i j k := by
  by_cases hij:j=i <;> by_cases hki:k=i <;> by_cases hkj:k=j
  all_goals simp_all [pairBound,variableExponent]

lemma sum_pairBound {n:ℕ} (i k:Fin (n+1)) :
    (∑ j:Fin (n+1),pairBound i j k)=if k=i then n else 1 := by
  by_cases hki:k=i
  · subst k
    simp only [pairBound,ite_true]
    simp only [Finset.sum_ite,Finset.sum_const_zero,zero_add,Finset.sum_const,smul_eq_mul,mul_one]
    have h:Finset.univ.filter (fun j:Fin (n+1) => ¬j=i)=Finset.univ.erase i := by ext j; simp [eq_comm]
    rw [h]
    simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
  · have hh (j:Fin (n+1)) : pairBound i j k=if j=k then 1 else 0 := by
      by_cases hj:j=i <;> by_cases hk:j=k <;> simp_all [pairBound,eq_comm]
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hki,ite_false]

lemma reflectionFactorL_box {n:ℕ} (i j:Fin n) :
    LaurentBox (reflectionFactorL i j) (pairBound i j) := by
  by_cases h:j=i
  · subst j
    rw [reflectionFactorL,ite_eq_left rfl]
    convert LaurentBox.one (n:=n) using 1
    funext k
    simp [pairBound]
  · rw [reflectionFactorL,ite_eq_right h]
    exact LaurentBox.sine _ _ _ (pairBound_add i j h)

lemma reducedMovingStepL_box {n:ℕ} (i j:Fin n) :
    LaurentMatrixBox (reducedMovingStepL i j) (fun k => 3*pairBound i j k) := by
  by_cases h:j=i
  · subst j
    rw [reducedMovingStepL,ite_eq_left rfl]
    convert LaurentMatrixBox.one (n:=n) (α:=Pairing (n+1)) using 1
    funext k
    simp [pairBound]
  · rw [reducedMovingStepL,ite_eq_right h]
    have hs:LaurentBox (constantL n (-4)*sineL (variableExponent i+variableExponent j) (phase^(-6:ℤ))) (pairBound i j) := by
      simpa using (LaurentBox.constant (-4)).mul (LaurentBox.sine _ _ _ (pairBound_add i j h))
    have hn:=torusNumeratorL_box (variableExponent i-variableExponent j) (phase^3) (pairBound i j) (pairBound_sub i j)
    have ht:LaurentMatrixBox
        (if i<j then rawLocal (PartialColumn.rowPosition (n:=n+1) j.val (by omega))
          (torusNumeratorL (variableExponent i-variableExponent j) (phase^3))
         else torusNumeratorL (variableExponent i-variableExponent j) (phase^3) .vacant • 1)
        (pairBound i j+pairBound i j) := by
      split_ifs
      · exact rawLocal_box _ _ _ hn
      · simpa using LaurentMatrixBox.smul (hn .vacant) LaurentMatrixBox.one
    convert LaurentMatrixBox.smul hs ht using 1
    funext k
    simp only [Pi.add_apply]
    omega

lemma nodalHeadL_box {n:ℕ} (i:Fin n) (occupied:Prop) [Decidable occupied] :
    LaurentBox (nodalHeadL i occupied) (selfBound i 2) := by
  have he:∀ k,-(selfBound i 2 k:ℤ)≤((2:ℤ) • variableExponent i) k ∧
      ((2:ℤ) • variableExponent i) k ≤ selfBound i 2 k := by
    intro k
    by_cases h:k=i <;> simp_all [selfBound,variableExponent]
  have hn:∀ k,-(selfBound i 2 k:ℤ)≤(-variableExponent i) k ∧
      (-variableExponent i) k ≤ selfBound i 2 k := by
    intro k
    by_cases h:k=i <;> simp_all [selfBound,variableExponent,Pi.single_apply]
  unfold nodalHeadL
  split_ifs
  · simpa using (LaurentBox.constant (4*c)).mul (LaurentBox.sine _ _ _ hn)
  · exact ((LaurentBox.cosine _ _ _ he).add (LaurentBox.cosine _ _ _ he)).add
      ((LaurentBox.constant rho).mono (fun k => Nat.zero_le _))

lemma deletionMapL_box {n m:ℕ} (r:ℕ) (hr:r+2≤n+2) :
    LaurentMatrixBox (deletionMapL (m:=m) r hr) 0 := by
  have hw:∀ t:Tile,LaurentBox ((deletionWeights : Weights (Laurent m)).tile t) 0 := by
    intro t
    cases t <;> simp only [Weights.tile,deletionWeights]
    all_goals first | exact LaurentBox.one | exact LaurentBox.zero _
  simpa only [deletionMapL,zero_add,Matrix.mul_assoc] using
    (rawLocal_box (PartialColumn.rowPosition r hr) _ _ hw).mul
      ((functionMatrix_box (n:=m) (Pairing.map (Fin.succAboveOrderEmb (⟨r+1,by omega⟩ : Fin (n+2))))).mul
        (functionMatrix_box (n:=m) (Pairing.map (Fin.succAboveOrderEmb (⟨r,by omega⟩ : Fin (n+1))))))

 
lemma nodalDatumL_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (i:Fin (n+1)) (p:Pairing (n+2)) :
    LaurentBox (nodalDatumL W i p) (fun k => if k=i then 4*n+2 else 2*n+2) := by
  have hr:=LaurentBox.prod Finset.univ (reflectionFactorL i) (pairBound i)
    (fun j _ => reflectionFactorL_box i j)
  have ht:=matrixPrefix_box (reducedMovingStepL i) (fun j k => 3*pairBound i j k)
    (reducedMovingStepL_box i)
  have hw:= (deletionMapL_box (m:=n+1) i.val (show i.val+2≤n+2 by omega)).mulVec
    (fun q => (hW q).insert i)
  have hres:= (hr.mul (nodalHeadL_box i (p.Occupied (Fin.last (n+1))))).mul
    (ht.mulVec hw p)
  apply hres.mono
  intro k
  simp only [Pi.add_apply,Finset.sum_apply,zero_add,←Finset.mul_sum,sum_pairBound]
  by_cases hk:k=i
  · subst k
    simp only [selfBound,ite_true,Fin.insertNth_apply_same]
    omega
  · obtain ⟨j,hj⟩:=Fin.exists_succAbove_eq hk
    rw [←hj,Fin.insertNth_apply_succAbove]
    simp only [Fin.succAbove_ne,ite_false,selfBound]
    have hn:1≤n := by have :=j.isLt; omega
    omega

end
end CriticalStrip.Diagram

end OAI
