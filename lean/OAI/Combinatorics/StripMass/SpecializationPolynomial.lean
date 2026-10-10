import Mathlib
import OAI.Combinatorics.StripMass.CollisionSubstitutions

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma RationalAt.eval₂ {R F K A:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] [CommRing A]
    (φ:R →+* K) (f:A →+* F) (g:A →+* K)
    (hfg:∀ a,RationalAt φ (f a) (g a)) {x:F} {y:K} (hxy:RationalAt φ x y)
    (P:Polynomial A) : RationalAt φ (P.eval₂ f x) (P.eval₂ g y) := by
  rw [Polynomial.eval₂_eq_sum,Polynomial.eval₂_eq_sum]
  exact RationalAt.sum _ _ _ (fun i _ => (hfg _).mul (hxy.pow i))

lemma RationalAt.eval_map {R F K:Type*} [CommRing R] [IsDomain R] [Field F] [Field K]
    [Algebra R F] [IsFractionRing R F] (φ:R →+* K)
    {x:F} {y:K} (hxy:RationalAt φ x y) (P:Polynomial R) :
    RationalAt φ ((P.map (Algebra.algebraMap R F)).eval x) ((P.map φ).eval y) := by
  simpa only [Polynomial.eval_map] using
    RationalAt.eval₂ φ (Algebra.algebraMap R F) φ RationalAt.algebraMap hxy P

lemma LastDegree.map {R K:Type*} [CommRing R] [CommRing K] {n m:ℕ}
    {P:Pairing (n+1) → Polynomial R} (hP:LastDegree m P) (φ:R →+* K) :
    LastDegree m (fun p => (P p).map φ) := by
  intro p k hk
  rw [Polynomial.coeff_map,hP p k hk,map_zero]

lemma LastDegree.of_map {R K:Type*} [CommRing R] [CommRing K] {n m:ℕ}
    {P:Pairing (n+1) → Polynomial R} (φ:R →+* K) (hφ:Function.Injective φ)
    (hP:LastDegree m (fun p => (P p).map φ)) : LastDegree m P := by
  intro p k hk
  apply hφ
  simpa only [Polynomial.coeff_map,map_zero] using hP p k hk


 

 


lemma liftLaurent_eq_insert {n:ℕ} (P:Laurent n) : liftLaurent P=insertLaurent (Fin.last n) P := by
  have he:liftLaurentHom n=insertLaurent (Fin.last n) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change liftLaurent (monomialL _ _)=insertLaurent (Fin.last n) (monomialL _ _)
    all_goals rw [liftLaurent_monomial,insertLaurent_monomial]
    all_goals congr 1
    all_goals ext i; induction i using Fin.lastCases <;> simp
  exact DFunLike.congr_fun he P

lemma lastExponent_eq_smul (n:ℕ) (a:ℤ) : lastExponent n a=a • variableExponent (Fin.last n) := by
  ext i
  induction i using Fin.lastCases <;> simp [lastExponent,variableExponent]

lemma lastCosine_eq (n:ℕ) : lastCosine n=cosineL ((2:ℤ) • variableExponent (Fin.last n)) (phase^3)⁻¹ := by
  unfold lastCosine cosineL
  rw [lastExponent_eq_smul,lastExponent_eq_smul]
  simp only [zpow_neg,zpow_ofNat,inv_inv,neg_smul]
  rfl

lemma lastCosine_map (n:ℕ) : evalLaurent (lastCosine n)=spectralA (Fin.last n) := by
  rw [lastCosine_eq,cosineL_map _ _ (inv_ne_zero (pow_ne_zero _ phase_ne_zero)),map_monomialL_two_variable]
  simp only [constF,map_inv₀,map_pow]
  congr 1
  simp [constF,div_eq_mul_inv,mul_comm]

lemma lastCosine_box (n:ℕ) : LaurentBox (lastCosine n) (selfBound (Fin.last n) 2) := by
  rw [lastCosine_eq]
  apply LaurentBox.cosine
  intro i
  by_cases hi:i=Fin.last n <;> simp [selfBound,variableExponent,hi]

lemma lastSine_box (n:ℕ) : LaurentBox (lastSine n) (selfBound (Fin.last n) 1) := by
  unfold lastSine
  apply LaurentBox.sub
  all_goals apply LaurentBox.single
  all_goals intro i; induction i using Fin.lastCases <;> simp [lastExponent,selfBound]

 
def lastLaurent {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n)) : Laurent (n+1) :=
  (if p.Occupied (Fin.last n) then lastSine n else 1)*P.eval₂ (liftLaurentHom n) (lastCosine n)

lemma lastLaurent_map {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n))
    (hP:P.map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p) :
    evalLaurent (lastLaurent p P)=rationalInterpolant n p := by
  have he:evalLaurent (P.eval₂ (liftLaurentHom n) (lastCosine n))=
      (rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
    rw [←hP,Polynomial.eval₂_map,←lastCosine_map]
    change (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) _ = _
    rw [Polynomial.hom_eval₂]
    have hh:(algebraMap (SpectralRing (n+1)) (SpectralField (n+1))).comp (liftLaurentHom n)=
        (liftSpectral n).comp (algebraMap (SpectralRing n) (SpectralField n)) := by
      apply RingHom.ext
      intro a
      exact (liftSpectral_evalLaurent a).symm
    rw [hh]
    rfl
  unfold lastLaurent rationalInterpolant
  rw [evalLaurent,map_mul]
  change evalLaurent (if p.Occupied (Fin.last n) then lastSine n else 1) *
    evalLaurent (P.eval₂ (liftLaurentHom n) (lastCosine n)) = _
  rw [he]
  congr 1
  split_ifs
  · exact evalLaurent_lastSine n
  · exact map_one _

lemma lastLaurent_box {n:ℕ} (p:Pairing (n+1)) (P:Polynomial (Laurent n))
    (hb:PolynomialBox P (fun _ => 2*n))
    (hd:∀ k,(if p.Occupied (Fin.last n) then n≤k else n<k) → P.coeff k=0) :
    LaurentBox (lastLaurent p P) (fun _ => 2*n) := by
  have hv:LaurentBox (P.eval₂ (liftLaurentHom n) (lastCosine n))
      (Fin.snoc (fun _ => 2*n) (if p.Occupied (Fin.last n) then 2*(n-1) else 2*n)) := by
    rw [Polynomial.eval₂_eq_sum]
    apply LaurentBox.sum
    intro k hk
    have hkz:P.coeff k≠0 := Polynomial.mem_support_iff.mp hk
    have hkdeg:if p.Occupied (Fin.last n) then k<n else k≤n := by
      split_ifs with hp
      · by_contra hh; exact hkz (hd k (by simp only [hp,ite_true]; omega))
      · by_contra hh; exact hkz (hd k (by simp only [hp,ite_false]; omega))
    have hi:=LaurentBox.insert (Fin.last n) (hb k)
    have hg:=hi.mul ((lastCosine_box n).pow k)
    change LaurentBox (liftLaurent (P.coeff k)*lastCosine n^k) _
    rw [liftLaurent_eq_insert]
    apply hg.mono
    intro j
    induction j using Fin.lastCases with
    | last =>
        simp only [Pi.add_apply,Fin.insertNth_apply_same,selfBound,zero_add,Fin.snoc_last]
        split_ifs at hkdeg ⊢ <;> omega
    | cast j =>
        simp only [Pi.add_apply]
        have hi:(Fin.insertNth (Fin.last n) 0 (fun _ => 2*n) : Fin (n+1) → ℕ) j.castSucc=2*n := by
          simpa only [Fin.succAbove_last] using Fin.insertNth_apply_succAbove (α:=fun _ => ℕ) (Fin.last n) 0 (fun _ => 2*n) j
        simp only [hi,Fin.snoc_castSucc,selfBound,Fin.castSucc_ne_last,ite_false,mul_zero,add_zero,le_refl]
  unfold lastLaurent
  by_cases hp:p.Occupied (Fin.last n)
  · have hn:0<n := by
      by_contra hh
      have he:n=0 := by omega
      subst n
      obtain ⟨j,hj⟩:=hp
      exact p.adj_irrefl _ (by simpa only [show j=Fin.last 0 by apply Fin.ext; omega] using hj)
    rw [ite_eq_left hp]
    apply ((lastSine_box n).mul hv).mono
    intro j
    induction j using Fin.lastCases with
    | last => simp only [Pi.add_apply,selfBound,Fin.snoc_last,hp,ite_true]; omega
    | cast j => simp [selfBound,hp]
  · rw [ite_eq_right hp,one_mul]
    apply hv.mono
    intro j
    induction j using Fin.lastCases <;> simp [hp]

end

 

 

noncomputable section
open Finset
open scoped Classical

@[simp] theorem liftSpectral_weights_tile {n : ℕ} (i : Fin n) (t : Tile) :
    liftSpectral n ((spectralWeights n i).tile t) =
      (spectralWeights (n+1) i.castSucc).tile t := by
  cases t <;> simp [spectralWeights, torusWeights, Weights.tile, torusL, map_div₀]

 

theorem spectralColumn_lastValue {n : ℕ} (P : Pairing (n+1) → Polynomial (SpectralField n)) :
    (spectralA (Fin.last n) + constF (n+1) C) •
      (column (spectralWeights (n+1))).mulVec
        (lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) P) =
      lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
        (lastTransform (fun i => (spectralWeights n i).tile)
          (constF n d) (constF n c) (constF n C) P) := by
  have h := rawColumn_lastValue (liftSpectral n) (fun i => (spectralWeights n i).tile)
    (constF n d) (constF n c) (constF n C)
    (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n)))
    (torusSin (constF (n+1) phase^3/variableF (Fin.last n)))
    (clearedSpectralRow (Fin.last n)) P
    (by simp)
    (by simp)
    (by simp)
    (by simp)
    (by simpa using spectral_sine_pair (Fin.last n))
  have hrow : Fin.snoc (fun i t => liftSpectral n ((spectralWeights n i).tile t))
      (clearedSpectralRow (Fin.last n)) =
      fun i t => (Fin.snoc (fun _ => 1) (spectralA (Fin.last n)+constF (n+1) C) :
        Fin (n+1) → SpectralField (n+1)) i * (spectralWeights (n+1) i).tile t := by
    funext i t
    induction i using Fin.lastCases with
    | last => simp only [Fin.snoc_last]; rfl
    | cast i => simp
  rw [hrow, rawColumn_scale, Matrix.smul_mulVec] at h
  simpa only [Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    prod_const_one, one_mul, ← column_eq_raw] using h

@[simp] theorem rationalInterpolant_eq_lastValue (n : ℕ) :
    rationalInterpolant n =
      lastValue (liftSpectral n) (spectralA (Fin.last n))
        (torusSin (variableF (Fin.last n))) (rationalNodalPolynomial n) := by
  funext p
  simp only [rationalInterpolant, lastValue]
  split_ifs <;> simp

 
theorem rationalInterpolationResidual_transfer {n : ℕ} (p : Pairing (n+1)) :
    rationalInterpolationResidual n p =
      ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) *
        lastValue (liftSpectral n) (spectralA (Fin.last n))
          (torusSin (variableF (Fin.last n))) (rationalResidualPolynomial n) p := by
  have ht := congrFun (spectralColumn_lastValue (rationalNodalPolynomial n)) p
  simp only [Pi.smul_apply, smul_eq_mul] at ht
  have hden := twice_rowDenominator (Fin.last n)
  unfold rationalInterpolationResidual
  rw [Fin.prod_univ_castSucc, rationalInterpolant_eq_lastValue]
  unfold rationalResidualPolynomial lastValue at *
  by_cases hp : p.Occupied (Fin.last n)
  · simp only [hp, ite_true, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, liftSpectral_const] at *
    rw [← hden] at ht ⊢
    linear_combination ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) * ht
  · simp only [hp, ite_false, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C, liftSpectral_const] at *
    rw [← hden] at ht ⊢
    linear_combination ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) * ht

 

theorem rationalInterpolationResidual_factor {n : ℕ} (p : Pairing (n+1)) :
    rationalInterpolationResidual n p =
      ((∏ i : Fin n, evalLaurent (rowDenominator i.castSucc)) / 2) *
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1) *
      liftSpectral n (rationalResidualCoefficient n p) *
      (Lagrange.nodal univ (@deletionBeta n)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
  rw [rationalInterpolationResidual_transfer]
  simp only [lastValue, rationalResidualPolynomial_factor, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  split_ifs <;> ring

end

 

 

noncomputable section
open scoped Classical

lemma rowDenominator_box {n:ℕ} (i:Fin n) : LaurentBox (rowDenominator i) (selfBound i 2) := by
  have h:∀j,-(selfBound i 1 j:ℤ)≤(-variableExponent i) j ∧ (-variableExponent i) j≤ selfBound i 1 j := by
    intro j
    by_cases h:j=i <;> simp [selfBound,variableExponent,h]
  convert sineL_product_box (-variableExponent i) (-variableExponent i) (phase^(5:ℤ)) (phase^(6:ℤ)) (selfBound i 1) h h using 1
  · rfl
  · funext j
    by_cases h:j=i <;> simp [selfBound,h]

lemma variableExponent_selfBound {n:ℕ} (i:Fin n) :
    ∀j,-(selfBound i 1 j:ℤ)≤variableExponent i j ∧ variableExponent i j≤ selfBound i 1 j := by
  intro j
  by_cases h:j=i <;> simp [selfBound,variableExponent,h]
lemma negVariableExponent_selfBound {n:ℕ} (i:Fin n) :
    ∀j,-(selfBound i 1 j:ℤ)≤(-variableExponent i) j ∧ (-variableExponent i) j≤ selfBound i 1 j := by
  intro j; have :=variableExponent_selfBound i j; simp only [Pi.neg_apply]; omega
lemma selfBound_one_add {n:ℕ} (i:Fin n) : selfBound i 1+selfBound i 1=selfBound i 2 := by
  funext j; by_cases h:j=i <;> simp [selfBound,h]

lemma rowNumerator_box {n:ℕ} (i:Fin n) (t:Tile) : LaurentBox (rowNumerator i t) (selfBound i 2) := by
  rw [←selfBound_one_add]
  cases t with
  | vacant => rw [selfBound_one_add]; exact rowDenominator_box i
  | vertical₀ => exact constant_sineL_box _ _ _ _ (variableExponent_selfBound i)
  | vertical₁ => exact constant_sineL_box _ _ _ _ (variableExponent_selfBound i)
  | cap => exact constant_sineL_box _ _ _ _ (negVariableExponent_selfBound i)
  | cup => exact constant_sineL_box _ _ _ _ (negVariableExponent_selfBound i)
  | diagonal₀ => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (variableExponent_selfBound i)
  | diagonal₁ => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (variableExponent_selfBound i)
  | verticalPair => exact sineL_product_box _ _ _ _ _ (variableExponent_selfBound i) (variableExponent_selfBound i)
  | capCup => exact sineL_product_box _ _ _ _ _ (negVariableExponent_selfBound i) (negVariableExponent_selfBound i)

lemma sum_selfBound (n a:ℕ) : (∑i:Fin n,selfBound i a)=fun _ =>a := by
  funext j
  simp [selfBound]

lemma rawColumn_box {n:ℕ} (w:Fin n → Tile → Laurent n)
    (h:∀i t,LaurentBox (w i t) (selfBound i 2)) :
    LaurentMatrixBox (rawColumn w) (fun _ =>2) := by
  intro p q
  unfold rawColumn
  apply LaurentBox.sum
  intro t _
  split_ifs
  · rw [←sum_selfBound n 2]
    exact LaurentBox.prod _ _ _ (fun i _ =>h i (t i))
  · exact LaurentBox.zero _

 

def laurentResidual {n:ℕ} (W:Pairing n → Laurent n) (p:Pairing n) : Laurent n :=
  (rawColumn rowNumerator).mulVec W p-(∏i:Fin n,rowDenominator i)*W p

lemma laurentResidual_box {n:ℕ} (W:Pairing n → Laurent n) (b:ℕ)
    (h:∀p,LaurentBox (W p) (fun _ =>b)) (p:Pairing n) :
    LaurentBox (laurentResidual W p) (fun _ =>b+2) := by
  apply LaurentBox.sub
  · exact ((rawColumn_box rowNumerator rowNumerator_box).mulVec h p).mono (by intro i; simp; omega)
  · have hd:LaurentBox (∏i:Fin n,rowDenominator i) (fun _ =>2) := by
      rw [←sum_selfBound n 2]
      exact LaurentBox.prod _ _ _ (fun i _ =>rowDenominator_box i)
    exact (hd.mul (h p)).mono (by intro i; simp; omega)

lemma laurentResidual_map {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (p:Pairing (n+1)) :
    evalLaurent (laurentResidual (fun p =>lastLaurent p (P p)) p)=rationalInterpolationResidual n p := by
  have hcol:(rawColumn (@rowNumerator (n+1))).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      (∏i:Fin (n+1),evalLaurent (rowDenominator i)) • column (spectralWeights (n+1)) := by
    rw [rawColumn_map]
    simp_rw [rowNumerator_map]
    rw [rawColumn_scale]
    rfl
  change (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) _=_
  rw [laurentResidual,map_sub,map_mul,map_prod]
  have he:(algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
      ((rawColumn rowNumerator).mulVec (fun p =>lastLaurent p (P p)) p)=
      (((rawColumn rowNumerator).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))).mulVec (rationalInterpolant n)) p := by
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro q _
    rw [show (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (lastLaurent q (P q))=rationalInterpolant n q from lastLaurent_map q (P q) (hP q)]
  rw [he,hcol,Matrix.smul_mulVec]
  change _ - _ * evalLaurent (lastLaurent p (P p))=_
  rw [lastLaurent_map p (P p) (hP p)]
  simp only [rationalInterpolationResidual,Pi.smul_apply,smul_eq_mul,mul_sub,evalLaurent]


 

 


lemma signLaurent_lift {n:ℕ} (i:Fin n) (f:Laurent n) :
    signLaurent i.castSucc (liftLaurent f)=liftLaurent (signLaurent i f) := by
  have he:(signLaurent i.castSucc).comp (liftLaurentHom n)=
      (liftLaurentHom n).comp (signLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change signLaurent i.castSucc (liftLaurent (monomialL _ _))=liftLaurent (signLaurent i (monomialL _ _))
    all_goals rw [liftLaurent_monomial,signLaurent_monomial,signLaurent_monomial,liftLaurent_monomial]
    all_goals simp only [Fin.snoc_castSucc]
  exact DFunLike.congr_fun he f

lemma signSpectral_lift {n:ℕ} (i:Fin n) (f:SpectralField n) :
    signSpectral i.castSucc (liftSpectral n f)=liftSpectral n (signSpectral i f) := by
  have he:(signSpectral i.castSucc).comp (liftSpectral n)=
      (liftSpectral n).comp (signSpectral i) := by
    apply IsFractionRing.ringHom_ext (A:=SpectralRing n)
    intro P
    change signSpectral i.castSucc (liftSpectral n (evalLaurent P))=liftSpectral n (signSpectral i (evalLaurent P))
    rw [liftSpectral_evalLaurent,signSpectral_evalLaurent,signSpectral_evalLaurent,liftSpectral_evalLaurent,signLaurent_lift]
  exact DFunLike.congr_fun he f

lemma rationalInterpolant_parity {n:ℕ} (i:Fin n) (p:Pairing (n+1)) :
    signSpectral i.castSucc (rationalInterpolant n p)=occupancySign p i.castSucc*rationalInterpolant n p := by
  have hp:=congrArg (fun P:Polynomial (SpectralField n) => P.eval₂ (liftSpectral n) (spectralA (Fin.last n)))
    (rationalNodalPolynomial_parity i p)
  simp only [Polynomial.eval₂_mul,Polynomial.eval₂_C] at hp
  have ho:liftSpectral n (occupancySign (K:=SpectralField n) p i.castSucc)=occupancySign p i.castSucc := by
    simp only [occupancySign]; split_ifs <;> simp
  rw [ho] at hp
  have hm:(signSpectral i.castSucc).comp (liftSpectral n)=(liftSpectral n).comp (signSpectral i) :=
    RingHom.ext (signSpectral_lift i)
  have hev:signSpectral i.castSucc ((rationalNodalPolynomial n p).eval₂ (liftSpectral n) (spectralA (Fin.last n)))=
      ((rationalNodalPolynomial n p).map (signSpectral i)).eval₂ (liftSpectral n) (spectralA (Fin.last n)) := by
    rw [Polynomial.hom_eval₂,hm,Polynomial.eval₂_map,signSpectral_spectralA]
  unfold rationalInterpolant
  rw [map_mul,hev,hp]
  have hs:signSpectral i.castSucc (torusSin (variableF (Fin.last n)))=torusSin (variableF (Fin.last n)) := by
    rw [signSpectral_torusSin,signSpectral_variable,ite_eq_right (Ne.symm (Fin.castSucc_ne_last i))]
  split_ifs <;> simp only [hs,map_one] <;> ring

lemma signSpectral_column {n:ℕ} (i:Fin n) (p q:Pairing n) :
    signSpectral i (column (spectralWeights n) p q)=
      occupancySign p i*occupancySign q i*column (spectralWeights n) p q := by
  have h:=column_map (signSpectral i) (spectralWeights n)
  rw [signSpectral_spectralWeights] at h
  have he:=congrArg (fun M:Matrix (Pairing n) (Pairing n) (SpectralField n) => M p q) h
  simpa only [Matrix.map_apply,column_signTwist] using he

lemma signSpectral_rowDenominator {n:ℕ} (i j:Fin n) :
    signSpectral i (evalLaurent (rowDenominator j))=evalLaurent (rowDenominator j) := by
  unfold evalLaurent
  rw [rowDenominator_map,signSpectral_torusL,map_div₀,map_pow,signSpectral_const,signSpectral_variable]
  split_ifs
  · have he : constF n phase ^ 3 / -variableF j = -(constF n phase ^ 3 / variableF j) := div_neg_eq_neg_div _ _
    rw [he,torusL_neg]
  · rfl

theorem rationalInterpolationResidual_parity {n:ℕ} (i:Fin n) (p:Pairing (n+1)) :
    signSpectral i.castSucc (rationalInterpolationResidual n p)=
      occupancySign p i.castSucc*rationalInterpolationResidual n p := by
  have hc:signSpectral i.castSucc ((column (spectralWeights (n+1))).mulVec (rationalInterpolant n) p)=
      occupancySign p i.castSucc*(column (spectralWeights (n+1))).mulVec (rationalInterpolant n) p := by
    simp only [Matrix.mulVec,dotProduct,map_sum,map_mul,signSpectral_column,rationalInterpolant_parity,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    calc
      _=occupancySign p i.castSucc*(occupancySign q i.castSucc*occupancySign q i.castSucc)*
        (column (spectralWeights (n+1)) p q*rationalInterpolant n q) := by ring
      _=_ := by rw [occupancySign_mul_self,mul_one]
  rw [rationalInterpolationResidual,map_mul,map_sub,map_prod]
  simp_rw [signSpectral_rowDenominator]
  rw [hc,rationalInterpolant_parity]
  ring

end

 

 

noncomputable section
open scoped Classical
open Finset

 
def LastMatrix {K:Type*} [Zero K] {n m:ℕ}
    (M:Matrix (Pairing (m+1)) (Pairing (n+1)) K) : Prop :=
  ∀p q, ¬(p.Occupied (Fin.last m) ↔ q.Occupied (Fin.last n)) → M p q=0

def matrixPolynomial {K:Type*} [CommRing K] {n m:ℕ}
    (M:Matrix (Pairing m) (Pairing n) K) (P:Pairing n → Polynomial K) :
    Pairing m → Polynomial K := fun p =>∑q,Polynomial.C (M p q)*P q

lemma matrixPolynomial_coeff {K:Type*} [CommRing K] {n m:ℕ}
    (M:Matrix (Pairing m) (Pairing n) K) (P:Pairing n → Polynomial K) (p:Pairing m) (k:ℕ) :
    (matrixPolynomial M P p).coeff k=M.mulVec (fun q =>(P q).coeff k) p := by
  simp only [matrixPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,Matrix.mulVec,dotProduct]

lemma LastMatrix.degree {K:Type*} [CommRing K] {n m d:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (P:Pairing (n+1) → Polynomial K) (hP:LastDegree d P) : LastDegree d (matrixPolynomial M P) := by
  intro p k hk
  rw [matrixPolynomial_coeff]
  apply sum_eq_zero
  intro q _
  change M p q*(P q).coeff k=0
  by_cases h:p.Occupied (Fin.last m) ↔ q.Occupied (Fin.last n)
  · rw [hP q k (by rwa [←h]),mul_zero]
  · rw [hM p q h,zero_mul]

lemma LastMatrix.lastValue {K:Type*} [CommRing K] {n m:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (b s:K) (P:Pairing (n+1) → Polynomial K) :
    lastValue (RingHom.id K) b s (matrixPolynomial M P)=
      M.mulVec (lastValue (RingHom.id K) b s P) := by
  funext p
  simp only [CriticalStrip.Diagram.lastValue,matrixPolynomial,Polynomial.eval₂_id,Polynomial.eval_finsetSum,
    Polynomial.eval_mul,Polynomial.eval_C,Matrix.mulVec,dotProduct]
  split_ifs with hp
  · rw [mul_sum]
    apply sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · simp only [hq,ite_true]; ring
    · rw [hM p q (by simp [hp,hq]),zero_mul,mul_zero]
      simp
  · apply sum_congr rfl
    intro q _
    by_cases hq:q.Occupied (Fin.last n)
    · rw [hM p q (by simp [hp,hq]),zero_mul,zero_mul]
    · simp [hq]

lemma LastMatrix.leading {K:Type*} [CommRing K] {n m d:ℕ}
    {M:Matrix (Pairing (m+1)) (Pairing (n+1)) K} (hM:LastMatrix M)
    (M':Matrix (Pairing m) (Pairing n) K)
    (h:∀p q,M p.padTop q.padTop=M' p q)
    (P:Pairing (n+1) → Polynomial K) (p:Pairing m) :
    (matrixPolynomial M P p.padTop).coeff d=M'.mulVec (fun q =>(P q.padTop).coeff d) p := by
  rw [matrixPolynomial_coeff]
  simp only [Matrix.mulVec,dotProduct]
  symm
  apply Fintype.sum_of_injective Pairing.padTop Pairing.padTop_injective
  · intro q hq
    have ho:q.Occupied (Fin.last n) := by
      by_contra hn
      exact hq ⟨q.restrict Fin.castSuccOrderEmb,Pairing.padTop_restrict q hn⟩
    rw [hM p.padTop q (by simp [ho]),zero_mul]
  · intro q; rw [h]

lemma LastMatrix.local {K:Type*} [CommRing K] {n:ℕ} (a:Position n) (w:Weights K) :
    LastMatrix (localR a.padTop w) := fun p q =>localR_padTop_zero_last a w q p

lemma LastMatrix.omit {K:Type*} [CommRing K] {n:ℕ} (r:Fin (n+1)) :
    LastMatrix (functionMatrix (K:=K) (Pairing.map (Fin.succAboveOrderEmb r.castSucc))) := by
  intro p q h
  unfold functionMatrix optionMatrix
  split_ifs with he
  · have hh:q.map (Fin.succAboveOrderEmb r.castSucc)=p := Option.some.inj he
    exfalso; apply h
    rw [←hh,←Pairing.omit_last r]
    exact Pairing.map_occupied _ q _
  · rfl

lemma LastMatrix.mul {K:Type*} [CommRing K] {n m r:ℕ}
    {M:Matrix (Pairing (r+1)) (Pairing (m+1)) K}
    {N:Matrix (Pairing (m+1)) (Pairing (n+1)) K}
    (hM:LastMatrix M) (hN:LastMatrix N) : LastMatrix (M*N) := by
  intro p q h
  apply sum_eq_zero; intro t _
  change M p t*N t q=0
  by_cases ht:p.Occupied (Fin.last r) ↔ t.Occupied (Fin.last m)
  · rw [hN t q (fun hh =>h (ht.trans hh)),mul_zero]
  · rw [hM p t ht,zero_mul]

end
end CriticalStrip.Diagram

end OAI
