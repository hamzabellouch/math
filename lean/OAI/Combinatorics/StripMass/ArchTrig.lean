import Mathlib
import OAI.Combinatorics.StripMass.ArchRoots

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical BigOperators

lemma arch_flat_constants : (c:ℂ) = (2*(d:ℂ)-1)*(C:ℂ) := by
  have hh : c=(2*d-1)*C := by
    rw [←c_add_rho_eq_C,rho_eq_two_c_d]
    linear_combination -(4*c)*d_sq
  exact_mod_cast hh

lemma fcos_arch_merge {n : ℕ} (i : Fin n) (k : ℤ) :
    fcos i (k-2)+fcos i (k+2)-fcos i k=constF n (2*(d:ℂ)-1)*fcos i k := by
  have h := (fcos_sum_product i k).1
  simp only [constF,map_sub,map_mul,map_ofNat,map_one] at *
  linear_combination h

lemma fcos_arch_delete {n : ℕ} (i : Fin n) :
    fcos i (-3)+fcos i 3 = -constF n (2*(d:ℂ)-1)*(fcos i (-9)+fcos i 9) := by
  have ha := (fcos_sum_product i (-1)).1
  have hb := (fcos_sum_product i 1).1
  have hc := fcos_sub_eight i (-1)
  have hd := fcos_eight i 1
  norm_num only at ha hb hc hd
  rw [hc,hd]
  simp only [constF,map_sub,map_mul,map_ofNat,map_one] at *
  linear_combination ha+hb

 

 


lemma pairEvaluation_rowCosine {n : ℕ} (s : ℕ) (i : Fin (n+2)) :
    pairEvaluation n s (rowCosineL i)=pairCosines n s i := by
  rw [pairEvaluation,torusEvaluation_rowCosine,pairPoint_cosine]

lemma mergeEvaluation_rowCosine {n : ℕ} (i : Fin (n+1)) :
    mergeEvaluation n (rowCosineL i)=
      (Fin.cons (fcos 0 (-1)) (fun j:Fin n => fcos j.succ (-3)) : Fin (n+1) → SpectralField (n+1)) i := by
  rw [mergeEvaluation,torusEvaluation_rowCosine]
  exact congrFun (mergePoint_cosines n) i

lemma deleteEvaluation_rowCosine {n : ℕ} (i : Fin n) :
    deleteEvaluation n (rowCosineL i)=fcos i.succ (-3) := by
  unfold deleteEvaluation
  exact (torusEvaluation_rowCosine (deletePoint n)
    (fun j => show deletePoint n j ≠ 0 from variableF_ne_zero j.succ) i).trans
      (congrFun (deletePoint_cosines n) i)

lemma nextScalar_flat_previous (n : ℕ) :
    previousCoeff (n+1) (nextScalar (algebraMap ℂ (SpectralField n)) (Fin.cons (constF n c) spectralA)) =
      (∏j:Fin n,(spectralA j+constF n C)) *
        (previousCoeff n (nextScalar (algebraMap ℂ (SpectralField n)) spectralA) +
          constF n C * scalarValue (algebraMap ℂ (SpectralField n)) spectralA) := by
  have hp := congrArg (previousCoeff (n+1)) (nextScalar_firstFlat n)
  rw [nextScalar_specialize] at hp
  simp only [firstFlatEvaluation_rowCosine,previousCoeff_C_mul,previousCoeff_linear,nextScalar_top] at hp
  exact hp

 

theorem archCandidate_firstFlat (n : ℕ) :
    firstFlatEvaluation n (archCandidate (n+1))=
      (∏j:Fin n,(spectralA j+constF n C))^2 * evalLaurent (archCandidate n) := by
  rw [archCandidate_specialize,archCandidate_eval]
  simp only [firstFlatEvaluation_rowCosine]
  unfold scalarArchNumerator
  have hs := scalarValue_flat (algebraMap ℂ (SpectralField n)) (@spectralA n)
  rw [show (algebraMap ℂ (SpectralField n)) (c:ℂ)=constF n c from rfl] at hs
  rw [hs,nextScalar_flat_previous]
  simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  have hc : constF n c=constF n (2*(d:ℂ)-1)*constF n C := by
    simpa only [constF,map_mul] using congrArg (constF n) arch_flat_constants
  change _ = (∏j:Fin n,(spectralA j+constF n C))^2 * _
  change constF n c = _ at hc
  change ((constF n c + ∑i:Fin n,spectralA i) * _ - _) = _
  simp only [constF] at hc ⊢
  rw [hc]
  ring

lemma nextScalar_merge_previous (n : ℕ) :
    previousCoeff (n+2) (nextScalar (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 2)) =
      mergePairScalar n *
        (previousCoeff (n+1) (nextScalar (algebraMap ℂ (SpectralField (n+1)))
          (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)))) +
          fcos 0 (-1) * scalarValue (algebraMap ℂ (SpectralField (n+1)))
            (Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)))) := by
  have hp := congrArg (previousCoeff (n+2)) (nextScalar_pair_merge n)
  rw [nextScalar_specialize,nextScalar_specialize] at hp
  simp only [pairEvaluation_rowCosine,mergeEvaluation_rowCosine,previousCoeff_C_mul] at hp
  rw [previousCoeff_linear (n+1),nextScalar_top] at hp
  exact hp

 
theorem archCandidate_merge (n : ℕ) :
    pairEvaluation n 2 (archCandidate (n+2))=
      mergePairScalar n^2 * mergeEvaluation n (archCandidate (n+1)) := by
  rw [archCandidate_specialize,archCandidate_specialize]
  simp only [pairEvaluation_rowCosine,mergeEvaluation_rowCosine]
  unfold scalarArchNumerator
  rw [scalar_pair_merge,nextScalar_merge_previous]
  have hc := fcos_arch_merge (0:Fin (n+1)) (-1)
  norm_num only at hc
  have hs : (∑i:Fin (n+2),pairCosines n 2 i)=
      (∑i:Fin (n+1),(Fin.cons (fcos 0 (-1)) (fun j:Fin n =>fcos j.succ (-3)) : Fin (n+1) → SpectralField (n+1)) i) +
        constF (n+1) (2*(d:ℂ)-1)*fcos 0 (-1) := by
    simp only [pairCosines,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    norm_num only
    linear_combination hc
  rw [hs]
  dsimp only [constF]
  ring

lemma nextScalar_delete_previous (n : ℕ) :
    previousCoeff (n+2) (nextScalar (algebraMap ℂ (SpectralField (n+1))) (pairCosines n 3)) =
      deletePairScalar n *
        (previousCoeff n (nextScalar (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3))) -
          (fcos 0 (-9)+fcos 0 9) * scalarValue (algebraMap ℂ (SpectralField (n+1))) (fun j:Fin n =>fcos j.succ (-3))) := by
  have hp := congrArg (previousCoeff (n+2)) (nextScalar_pair_delete n)
  rw [nextScalar_specialize,nextScalar_specialize] at hp
  simp only [pairEvaluation_rowCosine,deleteEvaluation_rowCosine,previousCoeff_C_mul] at hp
  rw [previousCoeff_quadratic _ _ _ _ (nextScalar_degree _ _),nextScalar_top] at hp
  exact hp

 
theorem archCandidate_delete (n : ℕ) :
    pairEvaluation n 3 (archCandidate (n+2))=
      deletePairScalar n^2 * deleteEvaluation n (archCandidate n) := by
  rw [archCandidate_specialize,archCandidate_specialize]
  simp only [pairEvaluation_rowCosine,deleteEvaluation_rowCosine]
  unfold scalarArchNumerator
  rw [scalar_pair_delete,nextScalar_delete_previous]
  have hc := fcos_arch_delete (0:Fin (n+1))
  have hs : (∑i:Fin (n+2),pairCosines n 3 i)=
      (∑j:Fin n,fcos j.succ (-3)) - constF (n+1) (2*(d:ℂ)-1)*(fcos 0 (-9)+fcos 0 9) := by
    simp only [pairCosines,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    norm_num only
    linear_combination hc
  rw [hs]
  dsimp only [constF]
  ring

 

 


def twoPair : Pairing 2 := ⟨{(0,1)}, by simp [IsPairing]⟩

@[simp] lemma twoPair_adj (i j : Fin 2) : twoPair.Adj i j ↔ (i=0 ∧ j=1) ∨ (i=1 ∧ j=0) := by
  simp [twoPair,Pairing.Adj,and_comm]

@[simp] lemma twoPair_occupied (i : Fin 2) : twoPair.Occupied i := by
  fin_cases i <;> simp [Pairing.Occupied]

def oneSourcePair : SourcePairing 1 := ⟨twoPair,twoPair_occupied _⟩

lemma SourcePairing.one_eq (p : SourcePairing 1) : p=oneSourcePair := by
  apply Subtype.ext
  apply Subtype.ext
  apply Finset.ext
  rintro ⟨i,j⟩
  have hu := p.val.property.1
  have hp := p.property
  change ∃ k, p.val.Adj (1:Fin 2) k at hp
  obtain ⟨k,hk⟩ := hp
  have hk0 : k=0 := by
    fin_cases k
    · rfl
    · exact False.elim (p.val.adj_irrefl 1 hk)
  subst k
  have hmem : (0,1) ∈ p.val.val := by
    rcases hk with hk|hk
    · have hh := hu _ hk; simp at hh
    · exact hk
  fin_cases i <;> fin_cases j <;> simp only [oneSourcePair,twoPair,Finset.mem_singleton,Prod.mk.injEq]
  all_goals aesop (add safe (by have : ¬((1:Fin 2)<0) := by decide; exact this))

instance : Subsingleton (SourcePairing 1) :=
  ⟨fun p q => p.one_eq.trans q.one_eq.symm⟩

lemma oneSourcePair_glues : Pairing.GluesAt (Fin.last 1) twoPair twoPair := by
  refine ⟨twoPair_occupied _,fun _ =>Iff.rfl,?_⟩
  intro i j hij
  fin_cases i
  · exact .single (Or.inl (by simp))
  · exact .refl

lemma sourceGlue_one {K : Type*} [CommRing K] (v w : SourcePairing 1 → K) :
    sourceGlue 1 v w=v oneSourcePair*w oneSourcePair := by
  rw [sourceGlue_eq_sum]
  simp only [Fintype.sum_subsingleton _ oneSourcePair,oneSourcePair,oneSourcePair_glues,ite_true,one_mul]

lemma sourceGlue_zero {K : Type*} [CommRing K] (v w : SourcePairing 0 → K) :
    sourceGlue 0 v w=0 := by
  have : IsEmpty (SourcePairing 0) := ⟨fun p =>p.ne_empty (p.val.eq_empty_of_le_one (by omega))⟩
  simp [sourceGlue, dotProduct]

lemma archCandidate_zero : archCandidate 0=0 := by
  simp [archCandidate,scalarArchNumerator,previousCoeff]

lemma polynomialNorthGluing_zero : polynomialNorthGluing 0=0 := sourceGlue_zero _ _

lemma empty_insertCup_two :
    (empty 2).insertCup 0 1 (by decide) (empty_not_occupied _) (empty_not_occupied _)=twoPair := by
  apply Subtype.ext
  simp [Pairing.insertCup,twoPair,empty]

lemma localR_deletion_twoPair {K : Type*} [Field K] :
    localR (PartialColumn.rowPosition 0 (show 2≤2 by omega)) (deletionWeights : Weights K) twoPair (empty 2)=1 := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single Tile.cup]
  · simp [Weights.tile,deletionWeights,optionMatrix,Pairing.tileStep,PartialColumn.rowPosition,empty_insertCup_two]
  · intro t _ ht
    cases t <;> simp_all [Weights.tile,deletionWeights,optionMatrix,Pairing.tileStep,
      PartialColumn.rowPosition]
    all_goals intro h; exact empty_not_occupied 0 (h ▸ twoPair_occupied 0)
  · simp

lemma deletionMap_zero_twoPair :
    (deletionMap (n:=0) (m:=1) 0 (by omega)).mulVec (fun _=>1) twoPair=1 := by
  let : Subsingleton (Pairing 0) := ⟨fun p q =>(p.eq_empty_of_le_one (by omega)).trans (q.eq_empty_of_le_one (by omega)).symm⟩
  rw [deletionMap]
  dsimp +instances only [CStarMatrix, CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid,
    CStarMatrix.ofMatrix, Equiv.refl, Equiv.symm]
  simp only [Equiv.coe_fn_mk, id_eq]
  simp only [Matrix.mulVec, dotProduct,Fintype.sum_subsingleton _ (empty 0),mul_one]
  rw [functionMatrix_mul,mul_functionMatrix]
  simpa only [Function.comp_apply,Pairing.map_empty] using (localR_deletion_twoPair (K:=SpectralField 1))

lemma reducedNodalDatum_one (p : SourcePairing 1) :
    reducedNodalDatum 0 p.val=4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) := by
  rw [p.one_eq]
  simp only [reducedNodalDatum,reducedNodalHead,oneSourcePair,twoPair_occupied,
    matrixPrefix,Nat.lt_succ_self,reducedMovingStep,↓reduceDIte,↓reduceIte,Matrix.mul_one]
  simp only [Fin.mk_zero,↓reduceIte,Matrix.one_mulVec]
  have hv : (fun q:Pairing 0 =>insertSpectral (0:Fin 1) (rationalVacuum 0 q))=fun _=>1 := by
    funext q
    rw [rationalVacuum_zero,map_one]
  rw [hv]
  change 4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) *
    (deletionMap (n:=0) (m:=1) 0 (by omega)).mulVec (fun _=>1) twoPair = _
  rw [deletionMap_zero_twoPair,mul_one]

lemma northNumerator_one (p : SourcePairing 1) :
    northNumerator 1 p=4*constF 1 c*torusSin (constF 1 phase^3/variableF 0) := by
  have hz : rationalNodalPolynomial 1 p.val=Polynomial.C ((rationalNodalPolynomial 1 p.val).coeff 0) := by
    apply Polynomial.eq_C_of_natDegree_le_zero
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    exact rationalNodalPolynomial_degree 1 p.val k (by simpa only [p.property,ite_true] using (show 1≤k by omega))
  have he := rationalNodalPolynomial_eval_div (0:Fin 1) p.val
  rw [hz,Polynomial.eval_C,reducedNodalDatum_eq] at he
  have hprod : (∏j:Fin 1,reflectionFactor (0:Fin 1) j)=1 := by
    apply Finset.prod_eq_one
    intro j _
    rw [Subsingleton.elim j 0]
    simp [reflectionFactor]
  rw [hprod,one_mul] at he
  exact he.trans (reducedNodalDatum_one p)

lemma polynomialNorthSource_one (p : SourcePairing 1) :
    evalLaurent (polynomialNorthSource 1 p)=
      (2*constF 1 c/constF 1 d)*torusSin (constF 1 phase^3/variableF 0) := by
  rw [polynomialNorthSource_eval_numerator,northNumerator_one]
  simp only [constF,map_div₀,map_mul,map_ofNat,map_one]
  ring

lemma scalarArchNumerator_one {K : Type*} [CommRing K] (f : ℂ →+* K) (a : Fin 1 → K) :
    scalarArchNumerator f a=a 0-f (2*(d:ℂ)-1)*(a 0+f (rho:ℂ)) := by
  have ha : a=fun _:Fin 1 =>a 0 := funext (fun i =>congrArg a (Subsingleton.elim i 0))
  rw [ha]
  unfold scalarArchNumerator
  rw [scalarValue_one]
  have he : nextScalar f (fun _:Fin 1=>a 0)=
      Polynomial.X+Polynomial.C (a 0)+Polynomial.C (f (rho:ℂ)) := by
    exact scalarValue_two (Polynomial.C.comp f) Polynomial.X (Polynomial.C (a 0))
  rw [he]
  simp [previousCoeff]

 

 


lemma arch_one_constants :
    ((2*(c:ℂ)/(d:ℂ))^2/2 = 2-2*(d:ℂ)) ∧
    ((2*(d:ℂ)-1)*(rho:ℂ)=(2-2*(d:ℂ))*(c:ℂ)) := by
  have hcs : 2*c^2 = 1-d := by
    have h := Real.cos_two_mul (3*lambda)
    rw [show 2*(3*lambda) = 6*lambda by ring,cos_six_lambda] at h
    change -d=2*c^2-1 at h
    linarith
  have hd : (d:ℂ)^2=(1/2:ℂ) := by
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using congrArg Complex.ofReal d_sq
  have hdz : (d:ℂ)≠0 := by exact_mod_cast d_ne_zero
  have hc : 2*(c:ℂ)^2=1-(d:ℂ) := by exact_mod_cast hcs
  constructor
  · rw [div_pow,mul_pow,hd]
    norm_num
    linear_combination 2*hc
  · have hr : (rho:ℂ)=2*(c:ℂ)*(d:ℂ) := by exact_mod_cast rho_eq_two_c_d
    rw [hr]
    linear_combination 4*(c:ℂ)*hd

lemma arch_one_field_constants (n : ℕ) :
    ((2*constF n c/constF n d)^2/2 = 2-2*constF n d) ∧
    (constF n (2*(d:ℂ)-1)*constF n rho=(2-2*constF n d)*constF n c) := by
  constructor
  · simpa only [constF,map_div₀,map_pow,map_mul,map_ofNat,map_sub]
      using congrArg (algebraMap ℂ (SpectralField n)) arch_one_constants.1
  · simpa only [constF,map_mul,map_ofNat,map_sub,map_one]
      using congrArg (algebraMap ℂ (SpectralField n)) arch_one_constants.2

lemma polynomialNorthGluing_one : polynomialNorthGluing 1=archCandidate 1 := by
  apply IsFractionRing.injective (SpectralRing 1) (SpectralField 1)
  change evalLaurent (polynomialNorthGluing 1)=evalLaurent (archCandidate 1)
  rw [polynomialNorthGluing_eval,sourceGlue_one,polynomialNorthSource_one,
    archCandidate_eval,scalarArchNumerator_one]
  simp only [map_mul,map_div₀,map_ofNat,map_pow,reflectSpectral_torusSin,
    reflectSpectral_const,reflectSpectral_variable]
  have hz : constF 1 phase^3/(constF 1 phase^3/variableF 0)=variableF (0:Fin 1) := by
    field_simp [constF_phase_ne_zero,variableF_ne_zero]
  rw [hz]
  have hs := spectral_sine_pair (0:Fin 1)
  have hc := arch_one_field_constants 1
  change _ = spectralA 0-constF 1 (2*(d:ℂ)-1)*(spectralA 0+constF 1 rho)
  have hleft : (2*constF 1 c/constF 1 d)*torusSin (variableF 0)*
      ((2*constF 1 c/constF 1 d)*torusSin (constF 1 phase^3/variableF 0)) =
      ((2*constF 1 c/constF 1 d)^2/2) *
        (2*torusSin (variableF 0)*torusSin (constF 1 phase^3/variableF 0)) := by ring
  rw [hleft,hs,hc.1]
  have hη : constF 1 (2*(d:ℂ)-1)=2*constF 1 d-1 := by
    simp only [constF,map_sub,map_mul,map_ofNat,map_one]
  rw [hη] at hc ⊢
  linear_combination hc.2

 

theorem polynomialNorthGluing_eq_archCandidate (n : ℕ) :
    polynomialNorthGluing n=archCandidate n := by
  induction n using Nat.twoStepInduction with
  | zero => rw [polynomialNorthGluing_zero,archCandidate_zero]
  | one => exact polynomialNorthGluing_one
  | more n ih₀ ih₁ =>
    apply sub_eq_zero.mp
    apply archLaurent_interpolation_zero
    · exact (polynomialNorthGluing_box _).sub (archCandidate_box _)
    · intro σ
      rw [map_sub,polynomialNorthGluing_permute,archCandidate_permute]
    · rw [map_sub,polynomialNorthGluing_parity,archCandidate_parity]
    · rw [map_sub,polynomialNorthGluing_row_reflection,archCandidate_row_reflection]
    · rw [map_sub,polynomialNorthGluing_firstFlat,archCandidate_firstFlat,ih₁,sub_self]
    · rw [map_sub,polynomialNorthGluing_merge,archCandidate_merge,ih₁,sub_self]
    · rw [map_sub,polynomialNorthGluing_delete,archCandidate_delete,ih₀,sub_self]

 

 


lemma scalarValue_allFlat_ne_zero (n : ℕ) :
    scalarValue (algebraMap ℂ (SpectralField 0)) (fun _:Fin n =>constF 0 c)≠0 := by
  have hc : constF 0 c+constF 0 C≠0 := by
    rw [←show constF 0 ((c:ℂ)+(C:ℂ))=constF 0 c+constF 0 C from map_add _ _ _]
    apply (map_ne_zero (algebraMap ℂ (SpectralField 0))).mpr
    have hC : 0<C := by
      unfold C lambda
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
    exact_mod_cast (ne_of_gt (add_pos (show 0<c by unfold c lambda; exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩) hC))
  induction n with
  | zero => rw [scalarValue_zero]; exact one_ne_zero
  | succ n ih =>
    have he : (fun _:Fin (n+1) => constF 0 c)=
        Fin.cons ((algebraMap ℂ (SpectralField 0)) (c:ℂ)) (fun _:Fin n =>constF 0 c) := by
      funext i
      induction i using Fin.cases <;> rfl
    rw [he,scalarValue_flat]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ =>hc)) ih

lemma allFlat_rowCosine (n : ℕ) (i : Fin n) :
    torusEvaluation (fun _:Fin n =>(1:SpectralField 0)) (fun _=>one_ne_zero) (rowCosineL i)=constF 0 c := by
  rw [torusEvaluation_rowCosine]
  simp only [one_pow,one_div,torusCos_inv,torusCos_phase_pow]
  rfl

 

theorem spectralNormalization_ne_zero (n : ℕ) : spectralNormalization n≠0 := by
  intro hz
  have hzero : scalarValue (constantL n) rowCosineL=0 := by
    apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
    change evalLaurent (scalarValue (constantL n) rowCosineL)=evalLaurent 0
    rw [scalarValue_rowCosine,polynomialVacuumVector_eval,rationalVacuum_empty,hz]
    exact (map_zero (algebraMap (SpectralRing n) (SpectralField n))).symm
  have he := congrArg (torusEvaluation (fun _:Fin n =>(1:SpectralField 0)) (fun _=>one_ne_zero)) hzero
  rw [scalarValue_specialize] at he
  simp only [allFlat_rowCosine,map_zero] at he
  exact scalarValue_allFlat_ne_zero n he

lemma scalarValue_spectral (n : ℕ) :
    scalarValue (algebraMap ℂ (SpectralField n)) spectralA=spectralNormalization n :=
  scalarPolynomial_eval_spectral n

 
def rationalArchPolynomial (n : ℕ) : Polynomial (SpectralField n) :=
  Polynomial.C (spectralNormalization n)⁻¹ *
    nextScalar (algebraMap ℂ (SpectralField n)) spectralA

lemma rationalArchPolynomial_coeff (n k : ℕ) :
    (rationalArchPolynomial n).coeff k=
      (nextScalar (algebraMap ℂ (SpectralField n)) spectralA).coeff k / spectralNormalization n := by
  rw [rationalArchPolynomial,Polynomial.coeff_C_mul]
  ring

 
theorem rationalArchPolynomial_monic_degree (n : ℕ) :
    (rationalArchPolynomial n).Monic ∧ (rationalArchPolynomial n).natDegree=n := by
  have ht : (rationalArchPolynomial n).coeff n=1 := by
    rw [rationalArchPolynomial_coeff,nextScalar_top,scalarValue_spectral,
      div_self (spectralNormalization_ne_zero _)]
  have hd : (rationalArchPolynomial n).natDegree≤n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [rationalArchPolynomial_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt
      ((nextScalar_degree _ _).trans_lt hk),zero_div]
  have he : (rationalArchPolynomial n).natDegree=n :=
    le_antisymm hd (Polynomial.le_natDegree_of_ne_zero (by rw [ht]; exact one_ne_zero))
  exact ⟨by rw [Polynomial.Monic,Polynomial.leadingCoeff,he,ht],he⟩

lemma previousCoeff_rationalArchPolynomial (n : ℕ) :
    previousCoeff n (rationalArchPolynomial n)=
      previousCoeff n (nextScalar (algebraMap ℂ (SpectralField n)) spectralA) / spectralNormalization n := by
  rw [rationalArchPolynomial,previousCoeff_C_mul]
  ring

 

theorem northSeparatorMoment_arch (n : ℕ) :
    northSeparatorMoment n = (∑i:Fin n,spectralA i) -
      constF n (2*(d:ℂ)-1)*previousCoeff n (rationalArchPolynomial n) := by
  have he := congrArg (@evalLaurent n) (polynomialNorthGluing_eq_archCandidate n)
  rw [polynomialNorthGluing_eval_moment,archCandidate_eval,scalarArchNumerator,
    scalarValue_spectral] at he
  change spectralNormalization n^2*northSeparatorMoment n =
    (∑i:Fin n,spectralA i)*spectralNormalization n^2-
      constF n (2*(d:ℂ)-1)*spectralNormalization n*
        previousCoeff n (nextScalar (algebraMap ℂ (SpectralField n)) spectralA) at he
  rw [previousCoeff_rationalArchPolynomial]
  apply (mul_left_cancel₀ (pow_ne_zero 2 (spectralNormalization_ne_zero n)))
  rw [mul_sub,he]
  field_simp [spectralNormalization_ne_zero n]

end
end CriticalStrip.Diagram

end OAI
