import Mathlib
import OAI.Combinatorics.StripMass.NodalRegularity

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset
open scoped Classical

lemma spectralA_injective (n : ℕ) : Function.Injective (@spectralA n) := by
  intro i j h
  by_contra hij
  rw [spectralA_shiftedCosine,spectralA_shiftedCosine] at h
  exact shiftedCosine_ne i j hij _ _ (zpow_ne_zero _ phase_ne_zero) h

lemma spectralA_ne_beta {n : ℕ} (i j : Fin n) : spectralA j≠deletionBeta i := by
  by_cases hij : j=i
  · subst j; exact spectralA_ne_deletionBeta i
  · rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine]
    exact shiftedCosine_ne j i hij _ _ (zpow_ne_zero _ phase_ne_zero)

def deletionScalarTuple {n : ℕ} (i : Fin (n+1)) : Fin (n+2) → SpectralField (n+1) :=
  twoCons (spectralA i) (deletionBeta i) (fun k => spectralA (i.succAbove k))

lemma deletionScalarTuple_injective {n : ℕ} (i : Fin (n+1)) :
    Function.Injective (deletionScalarTuple i) := by
  rw [deletionScalarTuple,←deletionPerm_tuple]
  apply Function.Injective.comp _ (deletionPerm i).injective
  intro j k h
  induction j using Fin.lastCases with
  | last =>
      induction k using Fin.lastCases with
      | last => rfl
      | cast k => exact (spectralA_ne_beta i k (by simpa using h.symm)).elim
  | cast j =>
      induction k using Fin.lastCases with
      | last => exact (spectralA_ne_beta i j (by simpa using h)).elim
      | cast k => exact congrArg Fin.castSucc (spectralA_injective _ (by simpa using h))

lemma spectralA_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) :
    discriminant (constF n d) (spectralA i) (spectralA j)≠0 := by
  rw [spectralA_shiftedCosine,spectralA_shiftedCosine]
  exact shiftedCosine_discriminant_ne i j hij _ _

lemma beta_spectralA_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) :
    discriminant (constF n d) (deletionBeta i) (spectralA j)≠0 := by
  rw [deletionBeta_shiftedCosine,spectralA_shiftedCosine]
  exact shiftedCosine_discriminant_ne i j hij _ _

lemma deletionScalarTuple_discriminant {n : ℕ} (i : Fin (n+1))
    (j k : Fin (n+2)) (hjk : j≠k)
    (hp : ¬((j=0 ∧ k=1) ∨ (j=1 ∧ k=0))) :
    discriminant (constF (n+1) d) (deletionScalarTuple i j) (deletionScalarTuple i k)≠0 := by
  induction j using Fin.cases with
  | zero =>
      induction k using Fin.cases with
      | zero => exact (hjk rfl).elim
      | succ k =>
          induction k using Fin.cases with
          | zero => exact (hp (Or.inl ⟨rfl,by simp⟩)).elim
          | succ k =>
              exact spectralA_discriminant_ne i (i.succAbove k) (Fin.succAbove_ne i k).symm
  | succ j =>
      induction j using Fin.cases with
      | zero =>
          induction k using Fin.cases with
          | zero => exact (hp (Or.inr ⟨by simp,rfl⟩)).elim
          | succ k =>
              induction k using Fin.cases with
              | zero => exact (hjk rfl).elim
              | succ k =>
                  exact beta_spectralA_discriminant_ne i (i.succAbove k) (Fin.succAbove_ne i k).symm
      | succ j =>
          induction k using Fin.cases with
          | zero =>
              exact spectralA_discriminant_ne (i.succAbove j) i (Fin.succAbove_ne i j)
          | succ k =>
              induction k using Fin.cases with
              | zero =>
                  rw [discriminant_symm]
                  exact beta_spectralA_discriminant_ne i (i.succAbove j) (Fin.succAbove_ne i j).symm
              | succ k =>
                  exact spectralA_discriminant_ne _ _ (fun he => hjk
                    (congrArg (fun x : Fin n => x.succ.succ) (Fin.succAbove_right_injective he)))

 

theorem nodalScalar_deletion {n : ℕ} (i : Fin (n+1)) :
    nodalScalar i=(spectralA i+deletionBeta i+constF (n+1) rho)*
      (∏ j : Fin n, (spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
        (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ)))) *
      MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField (n+1)))
        (fun j => spectralA (i.succAbove j)) (scalarPolynomial n d rho (by exact_mod_cast d_ne_zero)) := by
  rw [nodalScalar,scalarPolynomial_snoc_delete_reindex]
  exact scalarPolynomial_delete_roots (algebraMap ℂ (SpectralField (n+1))) n d rho _ _ _ _ _ _
    (deletionScalarTuple_injective i) (spectralA_roots i) (deletionBeta_roots i)
    (deletionScalarTuple_discriminant i)


 

 


 
def deletionDataFactor {n : ℕ} (i : Fin (n+1)) : SpectralField (n+1) :=
  (spectralA i+deletionBeta i+constF (n+1) rho)*
    ∏ j : Fin n, (spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ)))

lemma nodalScalar_factor_smaller {n : ℕ} (i : Fin (n+1)) :
    nodalScalar i=deletionDataFactor i*insertSpectral i (spectralNormalization n) := by
  rw [nodalScalar_deletion,insertSpectral_normalization]
  congr 1
  apply scalarPolynomial_eval
  · exact (spectralA_injective _).comp (Fin.succAbove_right_injective)
  · intro j k hjk
    exact spectralA_discriminant_ne _ _ (Fin.succAbove_right_injective.ne hjk)

lemma insertSpectral_rationalVacuum {n : ℕ} (i : Fin (n+1)) :
    (fun p => insertSpectral i (rationalVacuum n p))=
      insertSpectral i (spectralNormalization n) •
        normalizedVacuum (fun j => spectralWeights (n+1) (i.succAbove j)) := by
  funext p
  simp only [rationalVacuum,map_mul,insertSpectral_vacuum,Pi.smul_apply,smul_eq_mul]

 

theorem nodalVacuum_interpolation_data {n : ℕ} (i : Fin (n+1)) :
    nodalVacuum i = deletionDataFactor i •
      (movingBoxes i (n+1)).mulVec
        ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
          (fun p => insertSpectral i (rationalVacuum n p))) := by
  change nodalScalar i • normalizedVacuum (nodalWeights i)=_
  rw [nodalVacuum_movingBoxes,nodalScalar_factor_smaller,insertSpectral_rationalVacuum,
    Matrix.mulVec_smul,Matrix.mulVec_smul,smul_smul]

end

 

 

noncomputable section
open scoped Classical

 
def rawLocal {K : Type*} [CommRing K] {n : ℕ} (r : Position n) (w : Tile → K) :
    Matrix (Pairing n) (Pairing n) K :=
  ∑ t : Tile, w t • optionMatrix (fun p => p.tileStep r.left r.right r.adjacent t)

lemma rawLocal_weights {K : Type*} [CommRing K] {n : ℕ} (r : Position n) (w : Weights K) :
    rawLocal r w.tile=localR r w := rfl

lemma rawLocal_smul {K : Type*} [CommRing K] {n : ℕ} (r : Position n)
    (a : K) (w : Tile → K) : rawLocal r (fun t => a*w t)=a • rawLocal r w := by
  simp only [rawLocal,Finset.smul_sum,smul_smul]

 
def torusNumerator {n : ℕ} (z : SpectralField n) : Tile → SpectralField n
  | .vacant => torusL z
  | .cap | .cup => constF n d*torusSin z
  | .vertical₀ | .vertical₁ => constF n d*torusSin (constF n phase^3/z)
  | .diagonal₀ | .diagonal₁ => torusSin z*torusSin (constF n phase^3/z)
  | .verticalPair => torusSin (constF n phase^3/z)*torusSin (constF n phase^2/z)
  | .capCup => torusSin (z/constF n phase)*torusSin z

lemma torusNumerator_eq {n : ℕ} (z : SpectralField n) (hL : torusL z≠0) (t : Tile) :
    torusNumerator z t=torusL z*(torusWeights z).tile t := by
  cases t <;> simp only [torusNumerator,torusWeights,Weights.tile]
  all_goals field_simp

 

theorem movingBox_cleared {n m : ℕ} (i j : Fin n) (r : Position m) :
    ((spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
      (spectralA j-shiftedCosine i (phase^(9:ℤ)))) •
      localR r (torusWeights (constF n phase^3*(variableF i/variableF j))) =
    (-4*torusSin (variableF i*variableF j/constF n phase^6)*
      torusSin (constF n phase^3*(variableF i*variableF j))) •
      rawLocal r (torusNumerator (constF n phase^3*(variableF i/variableF j))) := by
  rw [movingBox_scalar_cancellation,←smul_smul]
  congr 1
  rw [←rawLocal_weights,←rawLocal_smul]
  congr 1
  funext t
  exact (torusNumerator_eq _ (torusL_deletion_ratio_ne_zero i j) t).symm

end

 

 

noncomputable section
open scoped Classical

variable {K L ι : Type*} [CommRing K] [CommRing L] [Fintype ι] [DecidableEq ι]

def matrixPrefix {n : ℕ} (A : Fin n → Matrix ι ι K) : ℕ → Matrix ι ι K
  | 0 => 1
  | k+1 => if h:k<n then A ⟨k,h⟩*matrixPrefix A k else matrixPrefix A k

lemma matrixPrefix_smul_partial {n : ℕ} (a : Fin n → K) (A : Fin n → Matrix ι ι K)
    (k : ℕ) :
    matrixPrefix (fun i => a i • A i) k=
      (∏ j∈Finset.range k,if h:j<n then a ⟨j,h⟩ else 1) • matrixPrefix A k := by
  induction k with
  | zero => simp [matrixPrefix]
  | succ k ih =>
    rw [matrixPrefix,Finset.prod_range_succ,matrixPrefix]
    by_cases hk:k<n
    · rw [dite_eq_left hk,dite_eq_left hk,dite_eq_left hk,ih,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
      congr 1
      exact mul_comm _ _
    · rw [dite_eq_right hk,dite_eq_right hk,dite_eq_right hk,mul_one,ih]

lemma matrixPrefix_smul {n : ℕ} (a : Fin n → K) (A : Fin n → Matrix ι ι K) :
    matrixPrefix (fun i => a i • A i) n=(∏ i,a i) • matrixPrefix A n := by
  rw [matrixPrefix_smul_partial,←Finset.prod_fin_eq_prod_range]

lemma matrixPrefix_map (f : K →+* L) {n : ℕ} (A : Fin n → Matrix ι ι K) (k : ℕ) :
    (matrixPrefix A k).map f=matrixPrefix (fun i => (A i).map f) k := by
  induction k with
  | zero => simp [matrixPrefix]
  | succ k ih =>
    rw [matrixPrefix,matrixPrefix]
    split_ifs with hk
    · rw [Matrix.map_mul,ih]
    · exact ih

end

 

 

noncomputable section

lemma rho_eq_two_c_d : rho=2*c*d := by
  have hc : 2*C*c=d := by
    have h₁:=Real.cos_add lambda (3*lambda)
    have h₂:=Real.cos_sub lambda (3*lambda)
    have he₁ : lambda+3*lambda=Real.pi/2 := by simp [lambda]; ring
    have he₂ : lambda-3*lambda=-(2*lambda) := by ring
    rw [he₁,Real.cos_pi_div_two] at h₁
    rw [he₂,Real.cos_neg] at h₂
    change 0=C*c-Real.sin lambda*Real.sin (3*lambda) at h₁
    change d=C*c+Real.sin lambda*Real.sin (3*lambda) at h₂
    linarith
  rw [rho_eq_inv_two_C]
  apply (div_eq_iff (by intro h; rw [h,zero_mul] at hc; exact d_ne_zero hc.symm)).mpr
  linear_combination -2*d*hc-2*d_sq

 
theorem deletion_occupied_sine_cancellation {n : ℕ} (i : Fin n) :
    spectralA i+deletionBeta i+constF n rho=
      4*constF n c*torusSin (deletionNode i)*
        torusSin (constF n phase^3/variableF i) := by
  have hq:=constF_phase_ne_zero n
  have hi:=variableF_ne_zero i
  have hβ : deletionBeta i=torusCos (variableF i^2*constF n phase^3) := by
    unfold deletionBeta deletionNode
    congr 1
    field_simp
  have hs:=torusCos_sum (variableF i^2) (constF n phase^3)
    (pow_ne_zero _ hi) (pow_ne_zero _ hq)
  rw [torusCos_phase_pow] at hs
  change spectralA i+torusCos (variableF i^2*constF n phase^3)=
    2*torusCos (variableF i^2)*constF n c at hs
  have hp:=torusSin_product (deletionNode i) (constF n phase^3/variableF i)
    (mul_ne_zero hi (pow_ne_zero _ hq)) (div_ne_zero (pow_ne_zero _ hq) hi)
  have he₁ : deletionNode i/(constF n phase^3/variableF i)=variableF i^2 := by
    unfold deletionNode
    field_simp
  have he₂ : deletionNode i*(constF n phase^3/variableF i)=constF n phase^6 := by
    unfold deletionNode
    field_simp
  rw [he₁,he₂,torusCos_phase_pow] at hp
  simp only [Nat.cast_ofNat,cos_six_lambda,Complex.ofReal_neg,constF,map_neg] at hp
  have hr:=congrArg (fun x : ℝ => constF n (x:ℂ)) rho_eq_two_c_d
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,constF,map_mul,map_ofNat] at hr
  rw [hβ]
  unfold constF at *
  linear_combination hs+hr-2*(algebraMap ℂ (SpectralField n)) (c:ℂ)*hp


 

 

open scoped Classical

 
def movingStep {n : ℕ} (i j : Fin n) : Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n) :=
  if i<j then localR (PartialColumn.rowPosition j.val (by omega))
      (torusWeights (constF n phase^3*(variableF i/variableF j))) else 1

lemma movingBoxes_prefix {n : ℕ} (i : Fin n) (k : ℕ) :
    movingBoxes i k=matrixPrefix (movingStep i) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [movingBoxes,matrixPrefix]
    by_cases hk:k<n
    · rw [dite_eq_left hk]
      by_cases hi:i.val<k
      · rw [dite_eq_left ⟨hi,hk⟩,ih,movingStep,ite_eq_left (show i<⟨k,hk⟩ from hi)]
      · rw [dite_eq_right (by omega),ih,movingStep,ite_eq_right (show ¬i<⟨k,hk⟩ from hi),Matrix.one_mul]
    · rw [dite_eq_right (by omega),dite_eq_right hk,ih]

 
def reflectionFactor {n : ℕ} (i j : Fin n) : SpectralField n :=
  if j=i then 1 else torusSin (constF n phase^3*(variableF i*variableF j))

def scalarPairFactor {n : ℕ} (i j : Fin n) : SpectralField n :=
  if j=i then 1 else (spectralA j-shiftedCosine i (phase^(-9:ℤ)))*
    (spectralA j-shiftedCosine i (phase^(9:ℤ)))

 

def reducedMovingStep {n : ℕ} (i j : Fin n) :
    Matrix (Pairing (n+1)) (Pairing (n+1)) (SpectralField n) :=
  if j=i then 1 else
    (-4*torusSin (variableF i*variableF j/constF n phase^6)) •
      if i<j then rawLocal (PartialColumn.rowPosition j.val (by omega))
        (torusNumerator (constF n phase^3*(variableF i/variableF j)))
      else torusL (constF n phase^3*(variableF i/variableF j)) • 1

lemma reducedMovingStep_eq {n : ℕ} (i j : Fin n) :
    scalarPairFactor i j • movingStep i j=reflectionFactor i j • reducedMovingStep i j := by
  by_cases hij:j=i
  · subst j
    simp [scalarPairFactor,reflectionFactor,reducedMovingStep,movingStep]
  · simp only [scalarPairFactor,reflectionFactor,reducedMovingStep,ite_eq_right hij]
    by_cases h:i<j
    · rw [ite_eq_left h,movingStep,ite_eq_left h,movingBox_cleared,smul_smul]
      congr 1
      ring
    · rw [ite_eq_right h,movingStep,ite_eq_right h,movingBox_scalar_cancellation,smul_smul,smul_smul]
      congr 1
      ring

lemma reducedMoving_product {n : ℕ} (i : Fin n) :
    (∏ j,scalarPairFactor i j) • movingBoxes i n=
      (∏ j,reflectionFactor i j) • matrixPrefix (reducedMovingStep i) n := by
  rw [movingBoxes_prefix,←matrixPrefix_smul,←matrixPrefix_smul]
  congr 1
  funext j
  exact reducedMovingStep_eq i j

lemma scalarPairFactor_product {n : ℕ} (i : Fin (n+1)) :
    (∏ j,scalarPairFactor i j)=
      ∏ j : Fin n,(spectralA (i.succAbove j)-shiftedCosine i (phase^(-9:ℤ)))*
        (spectralA (i.succAbove j)-shiftedCosine i (phase^(9:ℤ))) := by
  rw [Fin.prod_univ_succAbove _ i]
  simp [scalarPairFactor,Fin.succAbove_ne]

 

theorem nodalVacuum_reduced_data {n : ℕ} (i : Fin (n+1)) :
    nodalVacuum i =
      ((spectralA i+deletionBeta i+constF (n+1) rho)*∏ j,reflectionFactor i j) •
        (matrixPrefix (reducedMovingStep i) (n+1)).mulVec
          ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
            (fun p => insertSpectral i (rationalVacuum n p))) := by
  rw [nodalVacuum_interpolation_data,deletionDataFactor,←scalarPairFactor_product]
  rw [←smul_smul,←Matrix.smul_mulVec,reducedMoving_product,Matrix.smul_mulVec,smul_smul]

end

 

 

noncomputable section
open Finset
open scoped Classical

 
theorem rationalNodalPolynomial_at_node {n : ℕ} (p : Pairing (n+1)) (i : Fin n) :
    (if p.Occupied (Fin.last n) then torusSin (deletionNode i) else 1) *
      (rationalNodalPolynomial n p).eval (deletionBeta i) = nodalVacuum i p := by
  have hinj := (deletionBeta_injective n).injOn (s := (univ : Finset (Fin n)))
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [rationalNodalPolynomial, hp, ite_true]
    rw [Lagrange.eval_interpolate_at_node _ hinj (mem_univ _)]
    field_simp [deletionNode_sine_ne_zero i]
  · simp only [rationalNodalPolynomial, hp, ite_false, one_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_nodal_at_node (mem_univ _),
      mul_zero, zero_add]
    exact Lagrange.eval_interpolate_at_node _ hinj (mem_univ _)

theorem rationalNodalPolynomial_degree (n : ℕ) : LastDegree n (rationalNodalPolynomial n) := by
  intro p k hk
  have hinj := (deletionBeta_injective n).injOn (s := (univ : Finset (Fin n)))
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [rationalNodalPolynomial, hp, ite_true] at hk ⊢
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hdeg := Lagrange.degree_interpolate_lt
      (fun i => nodalVacuum i p / torusSin (deletionNode i)) hinj
    simp only [card_univ, Fintype.card_fin] at hdeg
    exact hdeg.trans_le (by exact_mod_cast hk)
  · simp only [rationalNodalPolynomial, hp, ite_false] at hk ⊢
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul]
    have hi := Lagrange.degree_interpolate_lt (fun i => nodalVacuum i p) hinj
    have hn := Lagrange.degree_nodal (s := (univ : Finset (Fin n))) (v := @deletionBeta n)
    simp only [card_univ, Fintype.card_fin] at hi hn
    rw [Polynomial.coeff_eq_zero_of_degree_lt (hi.trans_le (by exact_mod_cast Nat.le_of_lt hk)),
      Polynomial.coeff_eq_zero_of_degree_lt (hn.trans_lt (by exact_mod_cast hk)), mul_zero, add_zero]

theorem rationalNodalPolynomial_leading {n : ℕ} (p : Pairing n) :
    (rationalNodalPolynomial n p.padTop).coeff n = rationalVacuum n p := by
  simp only [rationalNodalPolynomial, Pairing.padTop_not_occupied_last, ite_false,
    Polynomial.coeff_add, Polynomial.coeff_C_mul]
  rw [Pairing.padTop, Pairing.restrict_map]
  have hnod : (Lagrange.nodal univ (@deletionBeta n)).coeff n = 1 := by
    simpa only [Lagrange.natDegree_nodal, card_univ, Fintype.card_fin] using
      (Lagrange.nodal_monic (s := (univ : Finset (Fin n))) (v := @deletionBeta n)).coeff_natDegree
  rw [hnod, mul_one, Polynomial.coeff_eq_zero_of_degree_lt, add_zero]
  simpa only [card_univ, Fintype.card_fin] using
    Lagrange.degree_interpolate_lt (s := univ) (fun i => nodalVacuum i (p.map Fin.castSuccOrderEmb))
      (deletionBeta_injective n).injOn

end

 

 

noncomputable section
open scoped Classical

lemma deletionBeta_eq {n : ℕ} (i : Fin n) :
    deletionBeta i=torusCos (constF n phase^3*variableF i^2) := by
  unfold deletionBeta deletionNode
  congr 1
  field_simp

lemma deletionBeta_difference {n : ℕ} (i j : Fin n) :
    deletionBeta i-deletionBeta j=
      -2*torusSin (constF n phase^3*(variableF i*variableF j))*
        torusSin (variableF i/variableF j) := by
  have hi:=variableF_ne_zero i
  have hj:=variableF_ne_zero j
  have hq:=constF_phase_ne_zero n
  have h:=torusSin_product (constF n phase^3*(variableF i*variableF j))
    (variableF i/variableF j)
    (mul_ne_zero (pow_ne_zero _ hq) (mul_ne_zero hi hj)) (div_ne_zero hi hj)
  have he₁ : (constF n phase^3*(variableF i*variableF j))/(variableF i/variableF j)=
      constF n phase^3*variableF j^2 := by field_simp
  have he₂ : (constF n phase^3*(variableF i*variableF j))*(variableF i/variableF j)=
      constF n phase^3*variableF i^2 := by field_simp
  rw [he₁,he₂,←deletionBeta_eq,←deletionBeta_eq] at h
  linear_combination h

def ordinaryFactor {n : ℕ} (i j : Fin n) : SpectralField n :=
  if j=i then 1 else -2*torusSin (variableF i/variableF j)

lemma deletionBeta_product {n : ℕ} (i : Fin n) :
    ((Finset.univ.erase i).prod (fun j : Fin n => deletionBeta i-deletionBeta j))=
      (∏ j,reflectionFactor i j)*(∏ j,ordinaryFactor i j) := by
  rw [←Finset.prod_mul_distrib]
  rw [←Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
    (fun j => reflectionFactor i j*ordinaryFactor i j) (Finset.mem_univ i)]
  simp only [reflectionFactor,ordinaryFactor,ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  have hij: j≠i := (Finset.mem_erase.mp hj).1
  rw [ite_eq_right hij,ite_eq_right hij,deletionBeta_difference]
  ring

lemma reflectionOrdinary_product_ne_zero {n : ℕ} (i : Fin n) :
    (∏ j,reflectionFactor i j)≠0 ∧ (∏ j,ordinaryFactor i j)≠0 := by
  apply mul_ne_zero_iff.mp
  rw [←deletionBeta_product]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr ((deletionBeta_injective n).ne (Ne.symm (Finset.mem_erase.mp hj).1))

def reducedNodalHead {n : ℕ} (i : Fin n) (occupied : Prop) [Decidable occupied] : SpectralField n :=
  if occupied then 4*constF n c*torusSin (constF n phase^3/variableF i)
  else spectralA i+deletionBeta i+constF n rho

 
def reducedNodalDatum {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) : SpectralField (n+1) :=
  reducedNodalHead i (p.Occupied (Fin.last (n+1))) *
    (matrixPrefix (reducedMovingStep i) (n+1)).mulVec
      ((deletionMap i.val (show i.val+2≤n+2 by omega)).mulVec
        (fun q => insertSpectral i (rationalVacuum n q))) p

lemma reducedNodalDatum_eq {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)=
      (∏ j,reflectionFactor i j)*reducedNodalDatum i p := by
  have h:=congrFun (nodalVacuum_reduced_data i) p
  simp only [Pi.smul_apply,smul_eq_mul] at h
  rw [h]
  unfold reducedNodalDatum reducedNodalHead
  by_cases hp:p.Occupied (Fin.last (n+1))
  · rw [ite_eq_left hp,ite_eq_left hp,deletion_occupied_sine_cancellation]
    field_simp [deletionNode_sine_ne_zero i]
  · rw [ite_eq_right hp,ite_eq_right hp,div_one]
    ring

lemma nodalWeight_reduced {n : ℕ} (i : Fin (n+1)) (p : Pairing (n+2)) :
    Lagrange.nodalWeight Finset.univ deletionBeta i *
      (nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))=
    reducedNodalDatum i p/(∏ j,ordinaryFactor i j) := by
  rw [reducedNodalDatum_eq,Lagrange.nodalWeight,Finset.prod_inv_distrib,deletionBeta_product]
  have h:=reflectionOrdinary_product_ne_zero i
  field_simp [h.1,h.2]

 

theorem nodal_interpolate_reduced {n : ℕ} (p : Pairing (n+2)) :
    Lagrange.interpolate Finset.univ deletionBeta
      (fun i : Fin (n+1) => nodalVacuum i p/
        (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))=
    ∑ i : Fin (n+1), Polynomial.C (reducedNodalDatum i p/(∏ j,ordinaryFactor i j))*
      Lagrange.nodal (Finset.univ.erase i) deletionBeta := by
  rw [Lagrange.interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Lagrange.nodal_erase_eq_nodal_div hi]
  rw [mul_right_comm,←map_mul,nodalWeight_reduced]

end
end CriticalStrip.Diagram

end OAI
