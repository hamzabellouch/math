import Mathlib
import OAI.Combinatorics.StripMass.FirstFlatSpecialization

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma torusEvaluation_rowNumerator {n m:ℕ} (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0) (i:Fin n) (t:Tile) :
    torusEvaluation z hz (rowNumerator i t)=torusEvaluation z hz (rowDenominator i)*
      (torusWeights (constF m phase^3/z i)).tile t := by
  let φ:Laurent n →ₐ[ℂ] SpectralField m:=torusEvaluation z hz
  have hn:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (rowNumerator i t)
  rw [rowNumerator_map] at hn
  apply hn.unique
  apply (RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField n) (rowDenominator i)).mul
  apply rationalAt_torusWeights
  · exact ((rationalAt_const φ phase).pow 3).div (rationalAt_variable z hz i) (hz i)
  · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero m)) (hz i)
  · exact hL i

lemma torusEvaluation_residual {n m:ℕ} (W:Pairing n → Laurent n)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0) (p:Pairing n) :
    torusEvaluation z hz (laurentResidual W p)=
      (∏i:Fin n,torusEvaluation z hz (rowDenominator i))*
        ((column (fun i =>torusWeights (constF m phase^3/z i))).mulVec
          (fun q =>torusEvaluation z hz (W q)) p-torusEvaluation z hz (W p)) := by
  let φ:Laurent n →ₐ[ℂ] SpectralField m:=torusEvaluation z hz
  have hm:(rawColumn (@rowNumerator n)).map φ.toRingHom=
      (∏i:Fin n,φ (rowDenominator i)) • column (fun i =>torusWeights (constF m phase^3/z i)) := by
    rw [rawColumn_map]
    dsimp only [φ,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom]
    simp_rw [torusEvaluation_rowNumerator z hz hL]
    rw [rawColumn_scale]
    rfl
  unfold laurentResidual
  rw [map_sub,map_mul,map_prod]
  have he:φ ((rawColumn rowNumerator).mulVec W p)=
      ((rawColumn rowNumerator).map φ.toRingHom).mulVec (fun q =>φ (W q)) p := by
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]
    rfl
  change φ ((rawColumn rowNumerator).mulVec W p)-_=_
  rw [he,hm,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul,mul_sub]
  rfl

lemma torusEvaluation_residual_zero {n m:ℕ} (W:Pairing n → Laurent n)
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0)
    (hL:∀i,torusL (constF m phase^3/z i)≠0)
    (hreg:VacuumRegular (fun i =>torusWeights (constF m phase^3/z i)))
    (a:SpectralField m)
    (hW:∀p,torusEvaluation z hz (W p)=a*normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)) p)
    (p:Pairing n) : torusEvaluation z hz (laurentResidual W p)=0 := by
  rw [torusEvaluation_residual W z hz hL]
  have hv:(fun q =>torusEvaluation z hz (W q))=a • normalizedVacuum (fun i =>torusWeights (constF m phase^3/z i)):=funext hW
  rw [hv,Matrix.mulVec_smul,(normalizedVacuum_stationary _ hreg).2]
  simp only [Pi.smul_apply,smul_eq_mul,hW,sub_self,mul_zero]


 

 


lemma permSpectral_rowDenominator {n:ℕ} (σ:Equiv.Perm (Fin n)) (i:Fin n) :
    permSpectral σ (evalLaurent (rowDenominator i))=evalLaurent (rowDenominator (σ i)) := by
  unfold evalLaurent
  rw [rowDenominator_map,rowDenominator_map,permSpectral_torusL,map_div₀,map_pow,permSpectral_const,permSpectral_variable]

lemma permSpectral_rowProduct {n:ℕ} (σ:Equiv.Perm (Fin n)) :
    permSpectral σ (∏i:Fin n,evalLaurent (rowDenominator i))=∏i:Fin n,evalLaurent (rowDenominator i) := by
  rw [map_prod]; simp_rw [permSpectral_rowDenominator]
  exact Equiv.prod_comp σ (fun i:Fin n => (evalLaurent (rowDenominator i):SpectralField n))

lemma permSpectral_column_map {n:ℕ} (σ:Equiv.Perm (Fin n)) :
    (column (spectralWeights n)).map (permSpectral σ)=column (fun i =>spectralWeights n (σ i)) := by
  rw [column_map]
  congr 1
  funext i
  exact permSpectral_spectralWeights σ i

lemma spectral_column_exchange {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    column (spectralWeights n)*localR (PartialColumn.rowPosition r hr)
          (torusWeights (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩))=
      localR (PartialColumn.rowPosition r hr)
          (torusWeights (variableF ⟨r+1,by omega⟩/variableF ⟨r,by omega⟩))*
        (column (spectralWeights n)).map (permSpectral (Equiv.swap ⟨r,by omega⟩ ⟨r+1,by omega⟩)) := by
  rw [permSpectral_column_map]
  apply PartialColumn.torus_column_exchange r hr (fun i =>constF n phase^3/variableF i)
  · exact div_ne_zero (variableF_ne_zero _) (variableF_ne_zero _)
  · exact div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero _)) (variableF_ne_zero _)
  · exact torusL_ratio_ne_zero _ _
  · rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero _
  · field_simp [variableF_ne_zero]

lemma matrix_residual_covariance {K:Type*} [CommRing K] {ι:Type*} [Fintype ι]
    (T R S:Matrix ι ι K) (v w:ι → K) (D:K)
    (hv:v=R.mulVec w) (hTR:T*R=R*S) :
    (fun p =>D*(T.mulVec v p-v p))=R.mulVec (fun p =>D*(S.mulVec w p-w p)) := by
  have h1:T.mulVec v=R.mulVec (S.mulVec w) := by
    rw [hv,Matrix.mulVec_mulVec,hTR,←Matrix.mulVec_mulVec]
  rw [h1,hv]
  change D • (R.mulVec (S.mulVec w)-R.mulVec w)=R.mulVec (D • (S.mulVec w-w))
  rw [Matrix.mulVec_smul,Matrix.mulVec_sub]

 
theorem rationalInterpolationResidual_covariance {n:ℕ} (r:ℕ) (hr:r+2≤n) :
    rationalInterpolationResidual n=
      (localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc / variableF (⟨r,by omega⟩:Fin n).castSucc))).mulVec
      (fun p =>permSpectral (topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)) (rationalInterpolationResidual n p)) := by
  let σ:=topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)
  let R:=localR (PartialColumn.rowPosition r hr).padTop
        (torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc / variableF (⟨r,by omega⟩:Fin n).castSucc))
  have he: column (spectralWeights (n+1))*R=R*(column (spectralWeights (n+1))).map (permSpectral σ) := by
    simpa only [R,σ,topPerm_swap,PartialColumn.rowPosition,Position.padTop,Fin.castSucc_mk] using
      spectral_column_exchange (n:=n+1) r (by omega)
  have hmap: (fun p =>permSpectral σ (rationalInterpolationResidual n p))=
      fun p =>(∏i:Fin (n+1),evalLaurent (rowDenominator i))*
        (((column (spectralWeights (n+1))).map (permSpectral σ)).mulVec
          (fun q =>permSpectral σ (rationalInterpolant n q)) p-permSpectral σ (rationalInterpolant n p)) := by
    funext p
    simp only [rationalInterpolationResidual,map_mul,map_sub,permSpectral_rowProduct,
      Matrix.mulVec,dotProduct,map_sum,Matrix.map_apply]
  rw [hmap]
  exact matrix_residual_covariance _ _ _ _ _ _ (rationalInterpolant_covariance r hr) he


 

 


lemma torusEvaluation_permLaurent {n m:ℕ} (σ:Equiv.Perm (Fin n))
    (z:Fin n → SpectralField m) (hz:∀i,z i≠0) (f:Laurent n) :
    torusEvaluation z hz (permLaurent σ f)=
      torusEvaluation (z ∘ σ) (fun i =>hz (σ i)) f := by
  have he:(torusEvaluation z hz).toRingHom.comp (permLaurent σ)=
      (torusEvaluation (z ∘ σ) (fun i =>hz (σ i))).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      change torusEvaluation z hz (permLaurent σ (monomialL 0 c))=
        torusEvaluation (z ∘ σ) _ (monomialL 0 c)
      simp only [permLaurent_monomial,torusEvaluation_monomial,
        Function.comp_apply,Pi.zero_apply,zpow_zero,
        Finset.prod_const_one,mul_one]
    · intro e
      change torusEvaluation z hz (permLaurent σ (monomialL e 1))=
        torusEvaluation (z ∘ σ) _ (monomialL e 1)
      rw [permLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
      congr 1
      simpa only [permExponent,AddMonoidHom.coe_mk,ZeroHom.coe_mk,Function.comp_apply,Equiv.symm_apply_apply] using
        (Equiv.prod_comp σ (fun i =>z i ^ (e ∘ σ.symm) i)).symm
  exact DFunLike.congr_fun he f

lemma rationalAt_localR {n k l:ℕ} (φ:Laurent k →ₐ[ℂ] SpectralField l)
    (a:Position n) (w:Weights (SpectralField k)) (v:Weights (SpectralField l))
    (h:∀t,RationalAt φ.toRingHom (w.tile t) (v.tile t)) (p q:Pairing n) :
    RationalAt φ.toRingHom (localR a w p q) (localR a v p q) := by
  simp only [localR,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply RationalAt.sum
  intro t _
  apply (h t).mul
  unfold optionMatrix
  split_ifs
  · exact RationalAt.one
  · exact RationalAt.zero

 

theorem residual_zero_transport {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (r:ℕ) (hr:r+2≤n) (z:Fin (n+1) → SpectralField m) (hz:∀i,z i≠0)
    (hL:torusL (z (⟨r+1,by omega⟩:Fin n).castSucc/z (⟨r,by omega⟩:Fin n).castSucc)≠0)
    (hzero:∀p,torusEvaluation
      (z ∘ topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩))
      (fun i =>hz _) (laurentResidual (fun p =>lastLaurent p (P p)) p)=0)
    (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun p =>lastLaurent p (P p)) p)=0 := by
  let σ:=topPerm (Equiv.swap (⟨r,by omega⟩:Fin n) ⟨r+1,by omega⟩)
  let φ:=torusEvaluation z hz
  let a:=(PartialColumn.rowPosition r hr).padTop
  let w:=torusWeights (variableF (⟨r+1,by omega⟩:Fin n).castSucc/variableF (⟨r,by omega⟩:Fin n).castSucc)
  let v:=torusWeights (z (⟨r+1,by omega⟩:Fin n).castSucc/z (⟨r,by omega⟩:Fin n).castSucc)
  have hw:∀t,RationalAt φ.toRingHom (w.tile t) (v.tile t) :=
    rationalAt_torusWeights φ ((rationalAt_variable z hz _).div (rationalAt_variable z hz _) (hz _))
      (div_ne_zero (hz _) (hz _)) hL
  have hv (q:Pairing (n+1)):RationalAt φ.toRingHom (permSpectral σ (rationalInterpolationResidual n q)) 0 := by
    have h:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
      (permLaurent σ (laurentResidual (fun p =>lastLaurent p (P p)) q))
    change RationalAt φ.toRingHom (evalLaurent _) _ at h
    rw [←permSpectral_evalLaurent,laurentResidual_map P hP] at h
    change RationalAt φ.toRingHom _ (torusEvaluation z hz _) at h
    rw [torusEvaluation_permLaurent] at h
    exact (hzero q) ▸ h
  have hright:=RationalAt.mulVec (φ:=φ.toRingHom) (localR a w) (localR a v)
    (fun q =>permSpectral σ (rationalInterpolationResidual n q)) (0:Pairing (n+1) → SpectralField m)
    (rationalAt_localR φ a w v hw) hv p
  have he:=congrFun (rationalInterpolationResidual_covariance r hr) p
  change rationalInterpolationResidual n p=(localR a w).mulVec _ p at he
  rw [←he,Matrix.mulVec_zero] at hright
  have hleft:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    (laurentResidual (fun p =>lastLaurent p (P p)) p)
  change RationalAt φ.toRingHom (evalLaurent _) _ at hleft
  rw [laurentResidual_map P hP] at hleft
  exact hleft.unique hright


 

 


lemma firstZeroRaw_smul {K:Type*} [CommRing K] {n:ℕ}
    (w:Fin n → Tile → K) (a:K) (v:Pairing n → K) :
    firstZeroRaw w (a • v)=a • firstZeroRaw w v := by
  have he:vacantBottomExtension (a • v)=a • vacantBottomExtension v := by
    funext p
    by_cases hp:p.Occupied 0 <;> simp [vacantBottomExtension,hp,Pi.smul_apply]
  rw [firstZeroRaw,he,Matrix.mulVec_smul]
  rfl

lemma rationalAt_firstFlat_weights {n:ℕ} (i:Fin (n+1)) (t:Tile) :
    RationalAt (firstFlatEvaluation n).toRingHom ((spectralWeights (n+1) i).tile t)
      (((Fin.cons deletionWeights (spectralWeights n) : Fin (n+1) → Weights (SpectralField n)) i).tile t) := by
  induction i using Fin.cases with
  | zero =>
      have hz:=rationalAt_firstFlat_variable (0:Fin (n+1))
      simp only [firstFlatPoint,Fin.cons_zero] at hz
      have h:=rationalAt_torusWeights (firstFlatEvaluation n)
        (((rationalAt_const _ phase).pow 3).div hz one_ne_zero)
        (by simpa using pow_ne_zero 3 (constF_phase_ne_zero n))
        (by rw [div_one,torusL_phase_three]; simpa only [torusL_one] using torusL_one_ne_zero n) t
      simpa only [spectralWeights,Fin.cons_zero,div_one,torusWeights_phase_three] using h
  | succ i =>
      have hz:=rationalAt_firstFlat_variable i.succ
      simp only [firstFlatPoint,Fin.cons_succ] at hz
      exact rationalAt_torusWeights (firstFlatEvaluation n)
        (((rationalAt_const _ phase).pow 3).div hz (variableF_ne_zero i))
        (div_ne_zero (pow_ne_zero _ (constF_phase_ne_zero n)) (variableF_ne_zero i))
        (by rw [←rowDenominator_map]; exact rowDenominator_map_ne_zero i) t

lemma rationalAt_firstFlat_normalization (n:ℕ) :
    RationalAt (firstFlatEvaluation n).toRingHom (spectralNormalization (n+1))
      ((∏ j : Fin n, (spectralA j+constF n C))*spectralNormalization n) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA (Fin.cons (constF n c) spectralA)
    (rationalAt_const (firstFlatEvaluation n)) rationalAt_firstFlat_spectralA
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  simp only [constF] at h
  rw [scalarPolynomial_eval_spectral,source_scalarPolynomial_flat,scalarPolynomial_eval_spectral] at h
  exact h

lemma rationalAt_firstFlat_vacuum {n:ℕ} (p:Pairing (n+1)) :
    RationalAt (firstFlatEvaluation n).toRingHom (rationalVacuum (n+1) p)
      ((∏ j : Fin n, (spectralA j+constF n C))*
        firstZeroRaw (fun j => (spectralWeights n j).tile) (rationalVacuum n) p) := by
  have hr:VacuumRegular (Fin.cons deletionWeights (spectralWeights n)) := by
    unfold VacuumRegular
    rw [det_flat_bottom _ (Or.inr rfl)]
    exact spectral_regular n
  have h:=rationalAt_normalizedVacuum _ _ rationalAt_firstFlat_weights hr p
  rw [normalizedVacuum_firstZero _ (spectral_regular n)] at h
  have he:= (rationalAt_firstFlat_normalization n).mul h
  have hs:rationalVacuum n=spectralNormalization n • normalizedVacuum (spectralWeights n) := rfl
  rw [hs,firstZeroRaw_smul]
  simpa only [rationalVacuum,Pi.smul_apply,smul_eq_mul,mul_assoc] using he

lemma deletionBeta_ne_const {n:ℕ} (i:Fin n) (z:ℂ) : deletionBeta i≠constF n z := by
  intro h
  have hc:evalLaurent (constantL n z)=constF n z := map_constantL _ _
  rw [←betaL_map,←hc] at h
  have he:betaL i=constantL n z := IsFractionRing.injective _ _ h
  have ht:(2:ℤ) • variableExponent i≠0 := by
    intro hh
    have hi:=congrFun hh i
    simp [variableExponent] at hi
  change betaL i=monomialL 0 z at he
  have hh:=congrArg (fun P:Laurent n => P.coeff ((2:ℤ) • variableExponent i)) he
  simp only [betaL,cosineL,monomialL,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right ht.symm,add_zero] at hh
  exact (pow_ne_zero 3 phase_ne_zero) ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

lemma firstFlatBeta_injective (n:ℕ) :
    Function.Injective (Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) := by
  intro i j h
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => exact (deletionBeta_ne_const j c (by simpa using h.symm)).elim
  | succ i =>
      induction j using Fin.cases with
      | zero => exact (deletionBeta_ne_const i c (by simpa using h)).elim
      | succ j => exact congrArg Fin.succ (deletionBeta_injective n (by simpa using h))

lemma firstFlatNode_sine_ne_zero {n:ℕ} (i:Fin (n+1)) :
    torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)≠0 := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,torusSin_phase_pow]
      apply (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr
      exact_mod_cast ne_of_gt sin_three_lambda_pos
  | succ i => exact deletionNode_sine_ne_zero i


 

 


lemma torus_firstZero_lastValue {n k:ℕ} (w:Fin n → Weights (SpectralField k))
    (z:SpectralField k) (hz:z≠0) (hL:torusL (constF k phase^3/z)≠0)
    (P:Pairing (n+1) → Polynomial (SpectralField k)) :
    (torusCos (z^2/constF k phase^3)+constF k C) •
      firstZeroRaw (fun i => ((Fin.snoc w (torusWeights (constF k phase^3/z)) :
        Fin (n+1) → Weights (SpectralField k)) i).tile)
        (lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z) P)=
      lastValue (RingHom.id _) (torusCos (z^2/constF k phase^3)) (torusSin z)
        (firstZeroPolynomial (fun i => (w i).tile) (constF k d) (constF k c) (constF k C) P) := by
  have h:=torus_last_cleared z hz hL
  have he:=firstZeroPolynomial_evaluation (RingHom.id _) (fun i => (w i).tile)
    (constF k d) (constF k c) (constF k C)
    (torusCos (z^2/constF k phase^3)) (torusSin z) (torusSin (constF k phase^3/z))
    (fun t => (torusCos (z^2/constF k phase^3)+constF k C)*
      (torusWeights (constF k phase^3/z)).tile t) P h.1 h.2.1 h.2.2.1 h.2.2.2
    (torus_sine_pair z hz)
  have hrow : Fin.snoc (fun i t => (RingHom.id (SpectralField k)) ((w i).tile t))
      (fun t => (torusCos (z^2/constF k phase^3)+constF k C)*
        (torusWeights (constF k phase^3/z)).tile t)=
      fun i t => (Fin.snoc (fun _ => 1) (torusCos (z^2/constF k phase^3)+constF k C) :
        Fin (n+1) → SpectralField k) i *
        ((Fin.snoc w (torusWeights (constF k phase^3/z)) : Fin (n+1) → Weights (SpectralField k)) i).tile t := by
    funext i t
    induction i using Fin.lastCases <;> simp
  rw [hrow,firstZeroRaw_rowScale] at he
  simpa only [Fin.prod_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,Finset.prod_const_one,one_mul] using he

lemma rationalAt_last_normalization {n:ℕ} (z:SpectralField n) (hz:z≠0) :
    RationalAt (lastEvaluation z hz).toRingHom (spectralNormalization (n+1))
      (MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))) := by
  have h:=RationalAt.mv_eval (algebraMap ℂ (SpectralField (n+1)))
    (algebraMap ℂ (SpectralField n)) spectralA
    (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
    (rationalAt_const (lastEvaluation z hz))
    (fun i => by
      induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last] using rationalAt_last_spectralA z hz
      | cast i => simpa only [Fin.snoc_castSucc,liftSpectral_spectralA] using
          rationalAt_last_lift z hz (spectralA i))
    (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero))
  rwa [scalarPolynomial_eval_spectral] at h

lemma rationalAt_last_vacuum {n:ℕ} (z:SpectralField n) (hz:z≠0)
    (hL:torusL (constF n phase^3/z)≠0)
    (hr:VacuumRegular (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z))))
    (p:Pairing (n+1)) :
    RationalAt (lastEvaluation z hz).toRingHom (rationalVacuum (n+1) p)
      ((MvPolynomial.eval₂Hom (algebraMap ℂ (SpectralField n))
        (Fin.snoc spectralA (torusCos (z^2/constF n phase^3)))
        (scalarPolynomial (n+1) d rho (by exact_mod_cast d_ne_zero)))*
        normalizedVacuum (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/z))) p) :=
  (rationalAt_last_normalization z hz).mul
    (rationalAt_normalizedVacuum _ _ (rationalAt_last_weights z hz hL) hr p)

 

lemma firstFlat_smaller_values {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (i:Fin (n+1)) (p:Pairing (n+1)) :
    lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (rationalNodalPolynomial n) p=
      firstFlatSmallerScalar n i * normalizedVacuum (firstFlatSmallerWeights n i) p := by
  induction i using Fin.cases with
  | succ i =>
      simp only [Fin.cons_succ,firstFlatSmallerScalar,firstFlatSmallerWeights]
      simpa only [lastValue,Polynomial.eval₂_id,nodalVacuum,ite_mul,one_mul] using rationalNodalPolynomial_at_node p i
  | zero =>
      have hz:constF n phase^3≠0:=pow_ne_zero _ (constF_phase_ne_zero n)
      have hdiv:constF n phase^3/(constF n phase^3)=1:=div_self hz
      have hcos:torusCos ((constF n phase^3)^2/constF n phase^3)=constF n c := by
        rw [pow_two,mul_div_cancel_right₀ _ hz,torusCos_phase_pow]
        rfl
      have hr:VacuumRegular (Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3/(constF n phase^3)))) := by
        rw [hdiv,torusWeights_one]
        exact firstFlatSmaller_regular n 0
      have h:=rationalAt_last_vacuum (constF n phase^3) hz
        (by rw [hdiv]; exact torusL_one_ne_zero n) hr p
      have he:=rationalAt_last_interpolant (constF n phase^3) hz p
      rw [hprev p] at he
      have heq:=he.unique h
      rw [hcos,hdiv,torusWeights_one] at heq
      simp only [constF] at heq
      rw [scalarPolynomial_eval_snoc_flat,scalarPolynomial_eval_spectral] at heq
      simpa only [firstFlatSmallerScalar,firstFlatSmallerWeights,Fin.cons_zero,constF] using heq


 

 


lemma firstFlatNode_ne_zero {n:ℕ} (i:Fin (n+1)) :
    (Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i≠0 := by
  induction i using Fin.cases with
  | zero => exact pow_ne_zero _ (constF_phase_ne_zero n)
  | succ i => exact mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))

lemma firstFlatNode_cosine {n:ℕ} (i:Fin (n+1)) :
    torusCos (((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)^2/
      constF n phase^3)=((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i) := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,pow_two,mul_div_cancel_right₀ _ (pow_ne_zero _ (constF_phase_ne_zero n)),torusCos_phase_pow]
      rfl
  | succ i => rfl

lemma firstFlatNode_L {n:ℕ} (i:Fin (n+1)) :
    torusL (constF n phase^3 / ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))≠0 := by
  induction i using Fin.cases with
  | zero =>
      rw [Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n))]
      exact torusL_one_ne_zero n
  | succ i =>
      have ha:constF n phase^3/deletionNode i=(variableF i)⁻¹ := by
        unfold deletionNode; field_simp [constF_phase_ne_zero]
      rw [Fin.cons_succ,ha,←inverseRowDenominator_map]
      exact inverseRowDenominator_map_ne_zero i

lemma firstFlatNode_weights {n:ℕ} (i:Fin (n+1)) :
    Fin.snoc (spectralWeights n) (torusWeights (constF n phase^3 /
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)))=
      firstFlatSmallerWeights n i := by
  induction i using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero,div_self (pow_ne_zero _ (constF_phase_ne_zero n)),
        torusWeights_one,firstFlatSmallerWeights]
  | succ i => rfl

lemma firstZeroPolynomial_flatNode {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (i:Fin (n+1)) (p:Pairing (n+2)) :
    lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (firstZeroPolynomial (fun j => (spectralWeights n j).tile)
        (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n)) p =
      (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
        firstFlatSmallerScalar n i * firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
          (normalizedVacuum (firstFlatSmallerWeights n i)) p := by
  have h:=torus_firstZero_lastValue (spectralWeights n)
    ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i)
    (firstFlatNode_ne_zero i) (firstFlatNode_L i) (rationalNodalPolynomial n)
  rw [firstFlatNode_cosine,firstFlatNode_weights] at h
  have hi: lastValue (RingHom.id _)
      ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)
      (torusSin ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i))
      (rationalNodalPolynomial n)=
      firstFlatSmallerScalar n i • normalizedVacuum (firstFlatSmallerWeights n i) := by
    funext q
    exact firstFlat_smaller_values hprev i q
  rw [hi,firstZeroRaw_smul] at h
  have he:=congrFun h p
  simpa only [Pi.smul_apply,smul_eq_mul,mul_assoc] using he.symm

 

theorem rationalNodalPolynomial_firstFlat {n:ℕ}
    (hprev:∀ p,rationalInterpolant n p=rationalVacuum (n+1) p)
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀ p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p) :
    (fun p => (P p).map (firstFlatEvaluation n).toRingHom)=
      fun p => Polynomial.C (∏ j:Fin n,(spectralA j+constF n C))*
        firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p := by
  have hdeg:LastDegree (n+1) P :=
    LastDegree.of_map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      (IsFractionRing.injective _ _)
      (by simpa only [hP] using rationalNodalPolynomial_degree (n+1))
  have hrightdeg:LastDegree (n+1) (fun p => Polynomial.C (∏ j:Fin n,(spectralA j+constF n C))*
        firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p) := by
    intro p k hk
    rw [Polynomial.coeff_C_mul,firstZeroPolynomial_degree _ _ _ _ _ (rationalNodalPolynomial_degree n) p k hk,mul_zero]
  apply lastPolynomial_unique _ _ (hdeg.map _) hrightdeg _ (firstFlatBeta_injective n)
  · intro p
    rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,
      firstZeroPolynomial_leading _ _ _ _ _ (rationalNodalPolynomial_degree n)]
    have hh: (fun q:Pairing n => (rationalNodalPolynomial n q.padTop).coeff n)=rationalVacuum n := by
      funext q; exact rationalNodalPolynomial_leading q
    rw [hh]
    have ha:=RationalAt.algebraMap (φ:=(firstFlatEvaluation n).toRingHom)
      (F:=SpectralField (n+1)) ((P p.padTop).coeff (n+1))
    have hb:=congrArg (fun Q:Polynomial (SpectralField (n+1)) => Q.coeff (n+1)) (hP p.padTop)
    rw [Polynomial.coeff_map,rationalNodalPolynomial_leading] at hb
    rw [hb] at ha
    exact ha.unique (rationalAt_firstFlat_vacuum p)
  · intro p i
    have hz:=firstFlatNode_ne_zero i
    have hs:=rationalAt_torusSin (firstFlatEvaluation n) (rationalAt_firstFlat_deletionNode i) hz
    have he: RationalAt (firstFlatEvaluation n).toRingHom
        ((rationalNodalPolynomial (n+1) p).eval (deletionBeta i))
        (((P p).map (firstFlatEvaluation n).toRingHom).eval
          ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)) := by
      rw [←hP]
      exact RationalAt.eval_map _ (rationalAt_firstFlat_deletionBeta i) _
    have hsin:RationalAt (firstFlatEvaluation n).toRingHom
        (if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)
        (if p.Occupied (Fin.last (n+1)) then torusSin
          ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1) := by
      split_ifs
      · exact hs
      · exact RationalAt.one
    have hb:=hsin.mul he
    rw [rationalNodalPolynomial_at_node] at hb
    have hv:=hb.unique (rationalAt_firstFlat_nodalVacuum i p)
    have hright:=firstZeroPolynomial_flatNode hprev i p
    apply mul_left_cancel₀ (show (if p.Occupied (Fin.last (n+1)) then torusSin
      ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1)≠0 by
        split_ifs; exact firstFlatNode_sine_ne_zero i; exact one_ne_zero)
    rw [hv,Polynomial.eval_mul,Polynomial.eval_C]
    have hr: (if p.Occupied (Fin.last (n+1)) then torusSin
        ((Fin.cons (constF n phase^3) deletionNode : Fin (n+1) → SpectralField n) i) else 1)*
        (firstZeroPolynomial (fun j => (spectralWeights n j).tile)
          (constF n d) (constF n c) (constF n C) (rationalNodalPolynomial n) p).eval
          ((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)=
        (((Fin.cons (constF n c) deletionBeta : Fin (n+1) → SpectralField n) i)+constF n C)*
          firstFlatSmallerScalar n i * firstZeroRaw (fun j => (firstFlatSmallerWeights n i j).tile)
            (normalizedVacuum (firstFlatSmallerWeights n i)) p := by
      simpa only [lastValue,Polynomial.eval₂_id,ite_mul,one_mul] using hright
    rw [mul_left_comm,hr]
    ring

end
end CriticalStrip.Diagram

end OAI
