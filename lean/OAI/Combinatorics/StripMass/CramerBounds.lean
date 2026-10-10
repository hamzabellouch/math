import Mathlib
import OAI.Combinatorics.StripMass.LaurentNumerator

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

lemma betaL_box {n:ℕ} (i:Fin n) : LaurentBox (betaL i) (selfBound i 2) := by
  apply LaurentBox.cosine
  intro k
  by_cases h:k=i <;> simp_all [selfBound,variableExponent]

lemma LaurentMatrixBox.det_terms {n m:ℕ} (A:Matrix (Fin m) (Fin m) (Laurent n))
    (b:Fin m → Fin m → Fin n → ℕ) (c:Fin n → ℕ)
    (hA:∀ i j,LaurentBox (A i j) (b i j))
    (hc:∀ σ:Equiv.Perm (Fin m),∀ k,(∑ j,b (σ j) j k)≤c k) : LaurentBox A.det c := by
  rw [Matrix.det_apply']
  apply LaurentBox.sum
  intro σ _
  have hp:LaurentBox (∏ j,A (σ j) j) c :=
    (LaurentBox.prod Finset.univ (fun j => A (σ j) j) (fun j => b (σ j) j)
      (fun j _ => hA (σ j) j)).mono (by simpa only [Finset.sum_apply] using hc σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs|hs
  · simpa only [hs,Units.val_one,Int.cast_one,one_mul] using hp
  · simpa only [hs,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul] using hp.neg

 

lemma interpolationNumerator_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (p:Pairing (n+2)) (a:Fin (n+1)) :
    LaurentBox (interpolationNumerator betaL (fun i => nodalDatumL W i p) a)
      (fun _ => 4*n+2) := by
  let dataBound:=fun (i k:Fin (n+1)) => if k=i then 4*n+2 else 2*n+2
  let b:=fun (i j k:Fin (n+1)) => if j=a then dataBound i k else if k=i then 2*j.val else 0
  apply LaurentMatrixBox.det_terms _ b
  · intro i j
    by_cases hj:j=a
    · subst j
      simpa only [Matrix.updateCol_apply,ite_true,b] using nodalDatumL_box W hW i p
    · rw [Matrix.updateCol_apply,ite_eq_right hj,Matrix.vandermonde_apply]
      have hh:LaurentBox (betaL i ^ j.val) (fun k => j.val*selfBound i 2 k) := (betaL_box i).pow j.val
      convert hh using 1
      funext k
      dsimp [b]
      rw [ite_eq_right hj]
      by_cases hk:k=i <;> simp [selfBound,hk,Nat.mul_comm]
  · intro σ k
    by_cases hk:k=σ a
    · have hb (j:Fin (n+1)) : b (σ j) j k=if j=a then 4*n+2 else 0 := by
        by_cases hj:j=a
        · subst j; simp [b,dataBound,hk]
        · have hkj:k≠σ j := by intro h; exact hj (σ.injective (h.symm.trans hk))
          simp [b,hj,hkj]
      simp only [hb,Finset.sum_ite_eq',Finset.mem_univ,ite_true,le_refl]
    · have hb (j:Fin (n+1)) : b (σ j) j k ≤
          (if j=a then 2*n+2 else 0)+(if j=σ.symm k then 2*j.val else 0) := by
        have hkj:k=σ j ↔ j=σ.symm k := by
          constructor
          · intro h; simpa only [Equiv.symm_apply_apply] using (congrArg σ.symm h).symm
          · intro h; simp only [h,Equiv.apply_symm_apply]
        by_cases hj:j=a
        · subst j; simp [b,dataBound,hk]
        · simp only [b,ite_eq_right hj,zero_add,hkj]
          exact le_refl _
      have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hb j)
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
      have hj: (σ.symm k).val<n+1 := (σ.symm k).isLt
      omega

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma constants_extreme_nonzero (n:ℕ) :
    constF n (phase^3/2)≠0 ∧ constF n ((phase^3)⁻¹/2)≠0 := by
  constructor
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (div_ne_zero (pow_ne_zero _ phase_ne_zero) (by norm_num))
  · exact (map_ne_zero (algebraMap ℂ (SpectralField n))).mpr (div_ne_zero (inv_ne_zero (pow_ne_zero _ phase_ne_zero)) (by norm_num))

lemma beta_difference_box {n:ℕ} (i j:Fin n) :
    LaurentBox (betaL j-betaL i) (fun k => 2*((if i=k then 1 else 0)+(if j=k then 1 else 0))) := by
  apply LaurentBox.sub
  · apply (betaL_box j).mono
    intro k
    by_cases hi:i=k <;> by_cases hj:j=k <;> simp_all [selfBound,eq_comm]
  · apply (betaL_box i).mono
    intro k
    by_cases hi:i=k <;> by_cases hj:j=k <;> simp_all [selfBound,eq_comm]

lemma beta_difference_exact {n:ℕ} (k i j:Fin (n+1)) (hij:i<j) :
    let b:ℤ := 2*((if i=k then 1 else 0)+(if j=k then 1 else 0))
    LaurentInterval (peelLaurent k (betaL j-betaL i)) (-b) b ∧
      (peelLaurent k (betaL j-betaL i)).coeff (-b)≠0 ∧
      (peelLaurent k (betaL j-betaL i)).coeff b≠0 := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · convert (beta_difference_box i j).peel k using 1 <;> push_cast <;> rfl
  all_goals
    have hn:=constants_extreme_nonzero n
    by_cases hi:i=k
    · subst i
      obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq (ne_of_gt hij)
      simp only [Fin.succAbove_ne,ite_false,add_zero,map_sub,
        AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_self,peel_beta_coeff_other]
      norm_num only [show (-2:ℤ)≠2 by omega,show (2:ℤ)≠ -2 by omega,show (2:ℤ)≠0 by omega,
        show (-2:ℤ)≠0 by omega,ite_true,ite_false,zero_add,add_zero,zero_sub,neg_ne_zero]
      first | exact hn.1 | exact hn.2
    · by_cases hj:j=k
      · subst j
        obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq hi
        simp only [Fin.succAbove_ne,ite_false,zero_add,map_sub,
          AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_self,peel_beta_coeff_other]
        norm_num only [show (-2:ℤ)≠2 by omega,show (2:ℤ)≠ -2 by omega,show (2:ℤ)≠0 by omega,
          show (-2:ℤ)≠0 by omega,ite_true,ite_false,zero_add,add_zero,sub_zero]
        first | exact hn.1 | exact hn.2
      · obtain ⟨s,rfl⟩:=Fin.exists_succAbove_eq hi
        obtain ⟨t,rfl⟩:=Fin.exists_succAbove_eq hj
        simp only [Fin.succAbove_ne,ite_false,zero_add,mul_zero,neg_zero,map_sub,
          AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,peel_beta_coeff_other,ite_true]
        apply sub_ne_zero.mpr
        exact (deletionBeta_injective n).ne (by intro h; subst t; exact lt_irrefl _ hij)

 

lemma vandermonde_beta_exact {n:ℕ} (k:Fin (n+1)) :
    let f:=peelLaurent k (Matrix.vandermonde (@betaL (n+1))).det
    LaurentInterval f (-(2*n:ℤ)) (2*n) ∧ f.coeff (-(2*n:ℤ))≠0 ∧ f.coeff (2*n)≠0 := by
  rw [Matrix.det_vandermonde,←prod_upperPair,map_prod]
  have hs:(∑ e:UpperPair (n+1),(2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))=2*n := by
    rw [←Finset.mul_sum]
    congr 1
    exact_mod_cast upperPair_incidence_sum k
  have hh:=LaurentInterval.prod_exact Finset.univ
    (fun e:UpperPair (n+1) => peelLaurent k (betaL e.val.2-betaL e.val.1))
    (fun e => -(2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))
    (fun e => (2*((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0)):ℤ))
    (fun e _ => beta_difference_exact k e.val.1 e.val.2 e.property)
  simpa only [Finset.sum_neg_distrib,hs] using hh

end

 

 

noncomputable section
open scoped Classical

def inlinePrivate155_signMonomial {n : ℕ} (i : Fin n) : Multiplicative (Fin n → ℤ) →* Laurent n where
  toFun e := monomialL e.toAdd ((-1:ℂ) ^ (e.toAdd i))
  map_one' := by simp [monomialL]; rfl
  map_mul' e f := by
    change monomialL (e.toAdd+f.toAdd) ((-1:ℂ) ^ (e.toAdd i+f.toAdd i)) = _
    rw [zpow_add₀ (by norm_num : (-1:ℂ)≠0)]
    exact (AddMonoidAlgebra.single_mul_single _ _ _ _).symm

def signLaurent {n : ℕ} (i : Fin n) : Laurent n →+* Laurent n :=
  (AddMonoidAlgebra.lift ℂ (Laurent n) (Fin n → ℤ) (inlinePrivate155_signMonomial i)).toRingHom

@[simp] lemma signLaurent_monomial {n : ℕ} (i : Fin n) (e : Fin n → ℤ) (z : ℂ) :
    signLaurent i (monomialL e z)=monomialL e (z * (-1:ℂ)^(e i)) := by
  change AddMonoidAlgebra.lift ℂ _ _ (inlinePrivate155_signMonomial i) (AddMonoidAlgebra.single e z)=_
  rw [AddMonoidAlgebra.lift_single]
  change z • AddMonoidAlgebra.single e ((-1:ℂ)^(e i))=AddMonoidAlgebra.single e _
  rw [AddMonoidAlgebra.smul_single,smul_eq_mul]

lemma signLaurent_involutive {n : ℕ} (i : Fin n) : Function.Involutive (signLaurent i) := by
  have h : (signLaurent i).comp (signLaurent i)=RingHom.id _ := by
    apply AddMonoidAlgebra.ringHom_ext <;> intro e
    all_goals change signLaurent i (signLaurent i (monomialL _ _))=monomialL _ _
    all_goals rw [signLaurent_monomial,signLaurent_monomial]
    all_goals congr 1; rw [mul_assoc,←mul_zpow]; norm_num
  intro f
  exact DFunLike.congr_fun h f

def signSpectral {n : ℕ} (i : Fin n) : SpectralField n →+* SpectralField n :=
  IsFractionRing.lift (K := SpectralField n)
    (g := (algebraMap (SpectralRing n) (SpectralField n)).comp (signLaurent i))
    ((IsFractionRing.injective (SpectralRing n) (SpectralField n)).comp
      (signLaurent_involutive i).injective)

@[simp] lemma signSpectral_evalLaurent {n : ℕ} (i : Fin n) (f : Laurent n) :
    signSpectral i (evalLaurent f)=evalLaurent (signLaurent i f) :=
  IsFractionRing.lift_algebraMap _ _

@[simp] lemma signSpectral_const {n : ℕ} (i : Fin n) (z : ℂ) :
    signSpectral i (constF n z)=constF n z := by
  have hc : constF n z=evalLaurent (constantL n z) := (map_constantL n z).symm
  rw [hc,signSpectral_evalLaurent]
  change evalLaurent (signLaurent i (monomialL 0 z))=evalLaurent (monomialL 0 z)
  rw [signLaurent_monomial]
  simp

@[simp] lemma signSpectral_variable {n : ℕ} (i j : Fin n) :
    signSpectral i (variableF j)=if j=i then -variableF j else variableF j := by
  change signSpectral i (evalLaurent (monomialL (variableExponent j) 1))=_
  rw [signSpectral_evalLaurent,signLaurent_monomial]
  by_cases h:j=i
  · subst j
    simp only [variableExponent,Pi.single_apply,ite_true,zpow_one,one_mul]
    change evalLaurent (AddMonoidAlgebra.single _ (-1)) = _
    rw [AddMonoidAlgebra.single_neg]
    simp only [evalLaurent,map_neg]
    rfl
  · have hi : i≠j := Ne.symm h
    simp only [variableExponent,Pi.single_apply,ite_eq_right hi,ite_eq_right h,zpow_zero,mul_one]
    rfl

@[simp] lemma signSpectral_torusSin {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusSin z)=torusSin (signSpectral i z) := by
  simp [torusSin,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma signSpectral_torusCos {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusCos z)=torusCos (signSpectral i z) := by
  simp [torusCos,map_div₀,map_inv₀,map_ofNat]

@[simp] lemma signSpectral_torusL {n : ℕ} (i : Fin n) (z : SpectralField n) :
    signSpectral i (torusL z)=torusL (signSpectral i z) := by simp [torusL]

@[simp] lemma signSpectral_torusWeights {n : ℕ} (i : Fin n) (z : SpectralField n) :
    (torusWeights z).map (signSpectral i)=torusWeights (signSpectral i z) := by
  simp [Weights.map,torusWeights,map_div₀]

end

 

 

noncomputable section
open scoped Classical
open Finset

 
def occupancySign {K : Type*} [Ring K] {n : ℕ} (p : Pairing n) (i : Fin n) : K :=
  if p.Occupied i then -1 else 1

def Weights.signTwist {K : Type*} [Ring K] (w : Weights K) : Weights K :=
  ⟨-w.A,w.B,-w.U,w.E,w.F⟩

@[simp] lemma occupancySign_empty {K : Type*} [Ring K] {n : ℕ} (i : Fin n) :
    occupancySign (K:=K) (empty n) i=1 := by simp [occupancySign]
@[simp] lemma occupancySign_mul_self {K : Type*} [Ring K] {n : ℕ} (p : Pairing n) (i : Fin n) :
    occupancySign (K:=K) p i*occupancySign p i=1 := by
  simp only [occupancySign]; split_ifs <;> simp

def inlinePrivate156_tileWest : Tile → Bool
  | .vertical₁ | .diagonal₁ | .cap | .verticalPair | .capCup => true
  | _ => false
def inlinePrivate156_tileEast : Tile → Bool
  | .vertical₀ | .diagonal₁ | .cup | .verticalPair | .capCup => true
  | _ => false
lemma inlinePrivate156_tileWest_iff (t : Tile) : t.Occupied 1 ↔ inlinePrivate156_tileWest t=true := by
  cases t <;> unfold Tile.Occupied Tile.Adj Tile.edges inlinePrivate156_tileWest <;> decide
lemma inlinePrivate156_tileEast_iff (t : Tile) : t.Occupied 2 ↔ inlinePrivate156_tileEast t=true := by
  cases t <;> unfold Tile.Occupied Tile.Adj Tile.edges inlinePrivate156_tileEast <;> decide

lemma Weights.signTwist_tile {K : Type*} [CommRing K] (w : Weights K) (t : Tile) :
    w.signTwist.tile t=(if t.Occupied 1 then -1 else 1)*
      (if t.Occupied 2 then -1 else 1)*w.tile t := by
  simp only [inlinePrivate156_tileWest_iff,inlinePrivate156_tileEast_iff]
  cases t <;> simp [signTwist,tile,inlinePrivate156_tileWest,inlinePrivate156_tileEast]

lemma column_signTwist {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (i : Fin n) (p q : Pairing n) :
    column (Function.update w i (w i).signTwist) q p=
      occupancySign q i * occupancySign p i * column w q p := by
  simp only [column,mul_sum]
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · have h (j : Fin n) : ((Function.update w i (w i).signTwist) j).tile (t j)=
        (if j=i then occupancySign q i * occupancySign p i else 1)*(w j).tile (t j) := by
      by_cases hj:j=i
      · subst j
        rw [Function.update_self,Weights.signTwist_tile]
        simp only [ht.west,ht.east,occupancySign,ite_true]
        ring
      · rw [Function.update_of_ne hj,ite_eq_right hj,one_mul]
    simp_rw [h]
    rw [prod_mul_distrib]
    simp
  · simp

lemma normalizedVacuum_signTwist {K : Type*} [Field K] {n : ℕ}
    (w : Fin n → Weights K) (i : Fin n) (hw : VacuumRegular w)
    (hs : VacuumRegular (Function.update w i (w i).signTwist)) :
    normalizedVacuum (Function.update w i (w i).signTwist)=
      fun p => occupancySign p i*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hs
  constructor
  · simp only [occupancySign_empty,one_mul]
    exact (normalizedVacuum_stationary w hw).1
  · funext q
    simp only [Matrix.mulVec,dotProduct,column_signTwist]
    have hh : ∀ p : Pairing n,
        occupancySign q i*occupancySign p i*column w q p*
          (occupancySign p i*normalizedVacuum w p)=
        occupancySign q i*(column w q p*normalizedVacuum w p) := by
      intro p
      calc
        _=occupancySign q i*(occupancySign p i*occupancySign p i)*
          (column w q p*normalizedVacuum w p) := by ring
        _=_ := by rw [occupancySign_mul_self,mul_one]
    simp_rw [hh]
    rw [←mul_sum]
    exact congrArg (occupancySign q i * ·) (congrFun (normalizedVacuum_stationary w hw).2 q)

end

 

 

noncomputable section
open scoped Classical

@[simp] lemma torusL_neg {n : ℕ} (z : SpectralField n) : torusL (-z)=torusL z := by
  simp only [torusL,mul_neg,torusSin_neg]
  ring

@[simp] lemma torusWeights_neg {n : ℕ} (z : SpectralField n) :
    torusWeights (-z)=(torusWeights z).signTwist := by
  have hinv : (-z)⁻¹ = -z⁻¹ := inv_neg
  simp only [torusWeights,Weights.signTwist,div_eq_mul_inv,hinv,
    mul_neg,torusSin_neg,torusL_neg,neg_mul,neg_neg]

@[simp] lemma signSpectral_spectralA {n : ℕ} (i j : Fin n) :
    signSpectral i (spectralA j)=spectralA j := by
  simp only [spectralA,signSpectral_torusCos,map_div₀,map_pow,signSpectral_const,
    signSpectral_variable]
  split_ifs <;> simp

lemma signSpectral_spectralWeights {n : ℕ} (i : Fin n) :
    (fun j => (spectralWeights n j).map (signSpectral i))=
      Function.update (spectralWeights n) i (spectralWeights n i).signTwist := by
  funext j
  simp only [spectralWeights,signSpectral_torusWeights,map_div₀,map_pow,signSpectral_const,
    signSpectral_variable]
  by_cases h:j=i
  · subst j
    simp only [ite_true,Function.update_self]
    have hh : constF n phase ^ 3 / -variableF i = -(constF n phase ^ 3 / variableF i) := div_neg_eq_neg_div _ _
    rw [hh,torusWeights_neg]
  · simp only [ite_eq_right h,Function.update_of_ne h]
    rfl

lemma signSpectral_vacuum {n : ℕ} (i : Fin n) (p : Pairing n) :
    signSpectral i (normalizedVacuum (spectralWeights n) p)=
      occupancySign p i*normalizedVacuum (spectralWeights n) p := by
  have hh:=normalizedVacuum_map (signSpectral i) (spectralWeights n) (spectral_regular n)
  have hr:VacuumRegular (Function.update (spectralWeights n) i (spectralWeights n i).signTwist) := by
    rw [←signSpectral_spectralWeights]
    exact (spectral_regular n).map (signSpectral i) (spectralWeights n)
  rw [signSpectral_spectralWeights,normalizedVacuum_signTwist _ _ (spectral_regular n) hr] at hh
  exact congrFun hh p

lemma signSpectral_normalization {n : ℕ} (i : Fin n) :
    signSpectral i (spectralNormalization n)=spectralNormalization n := by
  simp only [spectralNormalization,map_scalarNormalization,signSpectral_const,
    signSpectral_spectralA]

 
theorem rationalVacuum_sign {n : ℕ} (i : Fin n) (p : Pairing n) :
    signSpectral i (rationalVacuum n p)=occupancySign p i*rationalVacuum n p := by
  rw [rationalVacuum,map_mul,signSpectral_normalization,signSpectral_vacuum]
  ring


 

 


 

lemma normalizedVacuum_gauge {K : Type*} [Field K] {n : ℕ}
    (w v : Fin n → Weights K) (hw : VacuumRegular w) (hv : VacuumRegular v)
    (ε : Pairing n → K) (hε : ∀ p,ε p*ε p=1) (he : ε (empty n)=1)
    (hc : ∀ p q,column v q p=ε q*ε p*column w q p) :
    normalizedVacuum v=fun p => ε p*normalizedVacuum w p := by
  symm
  apply normalizedVacuum_unique _ hv
  constructor
  · change ε (empty n)*normalizedVacuum w (empty n)=1
    rw [he,(normalizedVacuum_stationary w hw).1,one_mul]
  · funext q
    simp only [Matrix.mulVec,dotProduct,hc]
    have hh (p : Pairing n) : ε q*ε p*column w q p*(ε p*normalizedVacuum w p)=
        ε q*(column w q p*normalizedVacuum w p) := by
      calc
        _=ε q*(ε p*ε p)*(column w q p*normalizedVacuum w p) := by ring
        _=_ := by rw [hε,mul_one]
    simp_rw [hh]
    rw [←Finset.mul_sum]
    exact congrArg (ε q * ·) (congrFun (normalizedVacuum_stationary w hw).2 q)


 

 


@[simp] lemma spectral_div_neg {n : ℕ} (x y : SpectralField n) :
    x/(-y)=-(x/y) := div_neg_eq_neg_div _ _

def doubleSignTwist {K : Type*} [Ring K] {n : ℕ} (w : Fin n → Weights K) (i j : Fin n) :=
  Function.update (Function.update w i (w i).signTwist) j (w j).signTwist

lemma column_doubleSignTwist {K : Type*} [CommRing K] {n : ℕ}
    (w : Fin n → Weights K) (i j : Fin n) (hij : j≠i) (p q : Pairing n) :
    column (doubleSignTwist w i j) q p=
      (occupancySign q i*occupancySign q j)*(occupancySign p i*occupancySign p j)*column w q p := by
  unfold doubleSignTwist
  conv_lhs => arg 1; arg 3; rw [←Function.update_of_ne hij (w i).signTwist w]
  rw [column_signTwist,column_signTwist]
  ring

@[simp] lemma signSpectral_deletionNode {n : ℕ} (k i : Fin n) :
    signSpectral k (deletionNode i)=if i=k then -deletionNode i else deletionNode i := by
  simp only [deletionNode,map_mul,signSpectral_variable,map_pow,signSpectral_const]
  split_ifs <;> simp

@[simp] lemma signSpectral_deletionBeta {n : ℕ} (k i : Fin n) :
    signSpectral k (deletionBeta i)=deletionBeta i := by
  simp only [deletionBeta,signSpectral_torusCos,map_div₀,map_pow,signSpectral_const,
    signSpectral_deletionNode]
  split_ifs <;> simp

lemma signSpectral_nodalScalar {n : ℕ} (k i : Fin n) :
    signSpectral k (nodalScalar i)=nodalScalar i := by
  have hc:(signSpectral k).comp (algebraMap ℂ (SpectralField n))=
      algebraMap ℂ (SpectralField n) := by
    ext z
    exact signSpectral_const k z
  have hv:(fun j : Fin (n+1) => signSpectral k
      ((Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) j))=
      (Fin.snoc spectralA (deletionBeta i) : Fin (n+1) → SpectralField n) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  rw [nodalScalar,MvPolynomial.map_eval₂Hom,hc,hv]

lemma signSpectral_nodalWeights {n : ℕ} (k i : Fin n) :
    (fun j => (nodalWeights i j).map (signSpectral k))=
      if i=k then doubleSignTwist (nodalWeights i) k.castSucc (Fin.last n)
      else Function.update (nodalWeights i) k.castSucc (nodalWeights i k.castSucc).signTwist := by
  funext j
  by_cases hi:i=k
  · simp only [ite_eq_left hi,doubleSignTwist]
    induction j using Fin.lastCases with
    | last =>
      simp only [nodalWeights,Fin.snoc_last,signSpectral_torusWeights,map_div₀,
        map_pow,signSpectral_const,signSpectral_deletionNode,ite_eq_left hi,Function.update_self]
      rw [spectral_div_neg,torusWeights_neg]
    | cast j =>
      rw [Function.update_of_ne (Fin.castSucc_ne_last j)]
      by_cases hj:j=k
      · subst j
        simp [nodalWeights,spectralWeights,map_div₀,spectral_div_neg]
      · have hj' : j.castSucc≠k.castSucc := fun h => hj (Fin.castSucc_injective n h)
        simp [nodalWeights,spectralWeights,map_div₀,hj,hj']
  · simp only [ite_eq_right hi]
    induction j using Fin.lastCases with
    | last =>
      simp only [nodalWeights,Fin.snoc_last,signSpectral_torusWeights,map_div₀,
        map_pow,signSpectral_const,signSpectral_deletionNode,ite_eq_right hi,
        Function.update_of_ne (Fin.castSucc_ne_last k).symm]
    | cast j =>
      by_cases hj:j=k
      · subst j
        simp [nodalWeights,spectralWeights,map_div₀,spectral_div_neg]
      · have hj' : j.castSucc≠k.castSucc := fun h => hj (Fin.castSucc_injective n h)
        simp [nodalWeights,spectralWeights,map_div₀,hj,hj']

def nodeSign {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) : SpectralField n :=
  occupancySign p k.castSucc * (if i=k then occupancySign p (Fin.last n) else 1)

lemma nodeSign_square {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    nodeSign k i p*nodeSign k i p=1 := by
  unfold nodeSign
  split_ifs
  · rw [mul_mul_mul_comm,occupancySign_mul_self,occupancySign_mul_self,one_mul]
  · simp

lemma signSpectral_nodalVacuum {n : ℕ} (k i : Fin n) (p : Pairing (n+1)) :
    signSpectral k (nodalVacuum i p)=nodeSign k i p*nodalVacuum i p := by
  have hcol (p q : Pairing (n+1)) :
      column (fun j => (nodalWeights i j).map (signSpectral k)) q p=
      nodeSign k i q*nodeSign k i p*column (nodalWeights i) q p := by
    rw [signSpectral_nodalWeights]
    by_cases hi:i=k
    · rw [ite_eq_left hi,column_doubleSignTwist _ _ _ (Fin.castSucc_ne_last k).symm]
      simp only [nodeSign,ite_eq_left hi]
    · rw [ite_eq_right hi,column_signTwist]
      simp only [nodeSign,ite_eq_right hi,mul_one]
  have hg:=normalizedVacuum_gauge (nodalWeights i)
    (fun j => (nodalWeights i j).map (signSpectral k)) (nodal_regular i)
    ((nodal_regular i).map (signSpectral k) (nodalWeights i)) (nodeSign k i)
    (nodeSign_square k i) (by simp [nodeSign]) hcol
  have hm:=normalizedVacuum_map (signSpectral k) (nodalWeights i) (nodal_regular i)
  rw [hg] at hm
  rw [nodalVacuum,map_mul,signSpectral_nodalScalar,congrFun hm p]
  ring

end
end CriticalStrip.Diagram

end OAI
