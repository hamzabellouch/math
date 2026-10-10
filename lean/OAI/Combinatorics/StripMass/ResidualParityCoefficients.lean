import Mathlib
import OAI.Combinatorics.StripMass.MergePairCandidate

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical LaurentPolynomial

lemma signLaurent_coeff {n:ℕ} (i:Fin n) (f:Laurent n) (e:Fin n → ℤ) :
    (signLaurent i f).coeff e=f.coeff e*(-1:ℂ)^(e i) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hf,hg]; ring
  | single a b =>
    change (signLaurent i (monomialL a b)).coeff e=_
    rw [signLaurent_monomial]
    simp only [monomialL,AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
    split_ifs with h
    · subst e; rfl
    · simp

lemma signLaurent_odd_even_coeff_zero {n:ℕ} (i:Fin n) (f:Laurent n)
    (h:signLaurent i f= -f) (e:Fin n → ℤ) (he:Even (e i)) : f.coeff e=0 := by
  have hh:=congrArg (fun g:Laurent n => g.coeff e) h
  rw [signLaurent_coeff,he.neg_one_zpow,mul_one,AddMonoidAlgebra.coeff_neg] at hh
  change f.coeff e= -f.coeff e at hh
  linear_combination (1/2:ℂ)*hh

lemma laurentResidual_odd {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc) :
    signLaurent i.castSucc (laurentResidual (fun q =>lastLaurent q (P q)) p)=
      -laurentResidual (fun q =>lastLaurent q (P q)) p := by
  apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
  change evalLaurent _=evalLaurent _
  rw [←signSpectral_evalLaurent,laurentResidual_map P hP,rationalInterpolationResidual_parity]
  simp only [occupancySign,hp,ite_true,neg_one_mul,evalLaurent,map_neg]
  congr 1
  exact (laurentResidual_map P hP p).symm

lemma laurentResidual_peel_top_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc) :
    (peelLaurent i.castSucc (laurentResidual (fun q =>lastLaurent q (P q)) p)).coeff (2*(n+1):ℤ)=0 := by
  by_contra h
  obtain ⟨e,he⟩:=(peelLaurent_coeff_ne_zero_iff _ _ _).mp h
  apply he
  apply signLaurent_odd_even_coeff_zero i.castSucc _ (laurentResidual_odd P hP i p hp)
  simp only [Fin.insertNth_apply_same]
  exact even_two_mul (n+1:ℤ)


 

 


lemma phase_primitive : IsPrimitiveRoot phase 16 := by
  have h:=Complex.isPrimitiveRoot_exp 16 (by norm_num)
  convert h using 2
  unfold phase lambda
  congr 1
  push_cast
  ring

 

def residualRootPhase {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : ℕ :=
  if j=i.castSucc then
    if k=0 then 0 else if k=1 then 8 else if k=2 then 3 else 11
  else if j=Fin.last n then
    if k=0 then 13 else if k=1 then 5 else if k=2 then 0 else 8
  else if j.val < i.val then
    if k=0 then 2 else if k=1 then 10 else if k=2 then 3 else 11
  else
    if k=0 then 14 else if k=1 then 6 else if k=2 then 13 else 5

def residualRootExponent {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : Fin (n+1) → ℤ :=
  if j=i.castSucc then 0 else if j=Fin.last n ∧ 2≤k.val then -variableExponent j else variableExponent j

def residualRoot {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) : SpectralField (n+1) :=
  evalLaurent (monomialL (residualRootExponent i v.1 v.2) (phase^(residualRootPhase i v.1 v.2)))

lemma residualRootPhase_lt {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) : residualRootPhase i j k<16 := by
  unfold residualRootPhase
  split_ifs <;> norm_num

lemma residualRootPhase_injective {n:ℕ} (i:Fin n) (j:Fin (n+1)) :
    Function.Injective (residualRootPhase i j) := by
  intro k l h
  by_cases hi:j=i.castSucc
  · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
  · by_cases hj:j=Fin.last n
    · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
    · by_cases hlt:j.val < i.val
      · fin_cases k <;> fin_cases l <;> simp_all [residualRootPhase]
      · simp only [residualRootPhase,ite_eq_right hi,ite_eq_right hj,ite_eq_right hlt] at h
        fin_cases k <;> fin_cases l <;> simp_all

lemma residualRootExponent_support {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) (l:Fin (n+1)) :
    residualRootExponent i j k l≠0 ↔ j≠i.castSucc ∧ l=j := by
  unfold residualRootExponent
  split_ifs <;> simp_all [variableExponent,Pi.single_apply]

lemma residualRootExponent_index {n:ℕ} (i:Fin n) (j l:Fin (n+1)) (k r:Fin 4)
    (h:residualRootExponent i j k=residualRootExponent i l r) : j=l := by
  by_cases hj:j=i.castSucc
  · by_contra hl
    have hl':l≠i.castSucc:=by intro e; exact hl (hj.trans e.symm)
    have he:residualRootExponent i l r l≠0 := (residualRootExponent_support i l r l).mpr ⟨hl',rfl⟩
    rw [←h] at he
    exact ((residualRootExponent_support i j k l).mp he).1 hj
  · have he:residualRootExponent i j k j≠0 := (residualRootExponent_support i j k j).mpr ⟨hj,rfl⟩
    rw [h] at he
    exact ((residualRootExponent_support i l r j).mp he).2

lemma residualRoot_ne_zero {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) : residualRoot i v≠0 := by
  unfold residualRoot
  intro h
  have he:monomialL (residualRootExponent i v.1 v.2) (phase^residualRootPhase i v.1 v.2)=0 :=
    IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)) (by simpa only [evalLaurent,map_zero] using h)
  exact pow_ne_zero _ phase_ne_zero (AddMonoidAlgebra.single_eq_zero.mp he)

lemma residualRoot_injective {n:ℕ} (i:Fin n) : Function.Injective (residualRoot i) := by
  rintro ⟨j,k⟩ ⟨l,r⟩ h
  have he:monomialL (residualRootExponent i j k) (phase^residualRootPhase i j k)=
      monomialL (residualRootExponent i l r) (phase^residualRootPhase i l r) :=
    IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1)) h
  have hh:=AddMonoidAlgebra.single_inj.mp he
  rcases hh with ⟨hex,hphase⟩ | ⟨hz,_⟩
  · have hj:=residualRootExponent_index i j l k r hex
    subst l
    have hk:=phase_primitive.pow_inj (residualRootPhase_lt i j k) (residualRootPhase_lt i j r) hphase
    exact Prod.ext rfl (residualRootPhase_injective i j hk)
  · exact (pow_ne_zero _ phase_ne_zero hz).elim

def residualRootSet {n:ℕ} (i:Fin n) : Finset (SpectralField (n+1)) :=
  Finset.univ.image (residualRoot i)

lemma residualRootSet_card {n:ℕ} (i:Fin n) : (residualRootSet i).card=4*(n+1) := by
  rw [residualRootSet,Finset.card_image_of_injective _ (residualRoot_injective i)]
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  omega

 

theorem residual_zero_of_root_grid {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (hb:∀p,LaurentBox (laurentResidual (fun q =>lastLaurent q (P q)) p) (fun _ =>2*(n+1)))
    (p:Pairing (n+1)) (i:Fin n) (hp:p.Occupied i.castSucc)
    (hz:∀v:Fin (n+1) × Fin 4,
      torusEvaluation (Function.update variableF i.castSucc (residualRoot i v))
        (fun j =>by by_cases h:j=i.castSucc <;> simp [h,residualRoot_ne_zero,variableF_ne_zero])
        (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    rationalInterpolationResidual n p=0 := by
  let f:=laurentResidual (fun q =>lastLaurent q (P q)) p
  have ht:(fullPeel i.castSucc f).coeff (2*(n+1):ℤ)=0 := by
    rw [fullPeel_coeff,laurentResidual_peel_top_zero P hP i p hp,map_zero]
  have hzero (z:SpectralField (n+1)) (h:z∈residualRootSet i):z≠0 := by
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp h
    exact residualRoot_ne_zero i v
  have hh:fullPeel i.castSucc f=0 := by
    apply laurent_root_saturation _ (2*(n+1)) ((hb p).fullPeel _) ht (residualRootSet i)
      (by rw [residualRootSet_card]; omega) hzero
    intro z h
    obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp h
    rw [fullPeel_eval]
    exact hz v
  have hf:f=0 := fullPeel_injective i.castSucc (by simpa only [map_zero] using hh)
  rw [←laurentResidual_map P hP,show laurentResidual (fun q =>lastLaurent q (P q)) p=f from rfl,hf]
  exact map_zero _

end

 

 

noncomputable section
open scoped Classical

lemma torusSin_monomial_ne_zero {n:ℕ} (e:Fin n → ℤ) (he:e≠0) (c:ℂ) (hc:c≠0) :
    torusSin (evalLaurent (monomialL e c))≠0 := by
  apply div_ne_zero _ (mul_ne_zero (by norm_num) ((map_ne_zero (algebraMap ℂ (SpectralField n))).mpr Complex.I_ne_zero))
  apply sub_ne_zero.mpr
  intro h
  rw [show (evalLaurent (monomialL e c))⁻¹=evalLaurent (monomialL (-e) c⁻¹) from map_monomialL_inv e c hc] at h
  have hh:=IsFractionRing.injective (SpectralRing n) (SpectralField n) h
  rcases AddMonoidAlgebra.single_inj.mp hh with ⟨heq,_⟩|⟨hz,_⟩
  · apply he
    funext i
    have hi:=congrFun heq i
    change e i= -e i at hi
    change e i=0
    omega
  · exact hc hz

lemma constF_mul_monomial {n:ℕ} (c d:ℂ) (e:Fin n → ℤ) :
    constF n c*evalLaurent (monomialL e d)=evalLaurent (monomialL e (c*d)) := by
  rw [←map_constantL]
  change evalLaurent (constantL n c)*evalLaurent (monomialL e d)=_
  unfold evalLaurent
  rw [←map_mul (algebraMap (SpectralRing n) (SpectralField n))]
  simp [constantL,monomialL,AddMonoidAlgebra.single_mul_single]

lemma torusL_monomial_ne_zero {n:ℕ} (e:Fin n → ℤ) (he:e≠0) (c:ℂ) (hc:c≠0) :
    torusL (evalLaurent (monomialL e c))≠0 := by
  unfold torusL
  have h (s:ℕ):constF n phase^s*evalLaurent (monomialL e c)=evalLaurent (monomialL e (phase^s*c)) := by
    change (algebraMap ℂ (SpectralField n)) phase^s*evalLaurent (monomialL e c)=_
    rw [←map_pow (algebraMap ℂ (SpectralField n))]; exact constF_mul_monomial _ _ _
  rw [h 2,h 3]
  exact mul_ne_zero (torusSin_monomial_ne_zero e he _ (mul_ne_zero (pow_ne_zero _ phase_ne_zero) hc))
    (torusSin_monomial_ne_zero e he _ (mul_ne_zero (pow_ne_zero _ phase_ne_zero) hc))

lemma monomial_ratio_regular {n:ℕ} (e f:Fin n → ℤ) (hef:e≠f) (c d:ℂ) (hc:c≠0) (hd:d≠0) :
    torusL (evalLaurent (monomialL e c)/evalLaurent (monomialL f d))≠0 := by
  rw [div_eq_mul_inv,show (evalLaurent (monomialL f d))⁻¹=evalLaurent (monomialL (-f) d⁻¹) from map_monomialL_inv f d hd]
  unfold evalLaurent
  rw [←map_mul (algebraMap (SpectralRing n) (SpectralField n))]
  rw [monomialL_mul]
  apply torusL_monomial_ne_zero _ _ _ (mul_ne_zero hc (inv_ne_zero hd))
  simpa only [←sub_eq_add_neg,sub_ne_zero] using hef

lemma variableExponent_injective {n:ℕ} : Function.Injective (@variableExponent n) := by
  intro i j h
  by_contra hij
  have hh:=congrFun h i
  simp [variableExponent,hij] at hh

lemma flat_update_regular {n:ℕ} (i j:Fin n) (hij:i≠j) (c:ℂ) (hc:c≠0) :
    torusL ((Function.update variableF i.castSucc (constF (n+1) c)) i.castSucc/
      (Function.update variableF i.castSucc (constF (n+1) c)) j.castSucc)≠0 := by
  simp only [Function.update_self,Function.update_of_ne (fun h =>hij (Fin.castSucc_injective n h).symm)]
  change torusL (evalLaurent (monomialL 0 c)/evalLaurent (monomialL (variableExponent j.castSucc) 1))≠0
  apply monomial_ratio_regular _ _ _ c 1 hc one_ne_zero
  intro h
  have hh:=congrFun h j.castSucc
  simp [variableExponent] at hh

lemma pair_update_regular {n:ℕ} (i j:Fin n) (_hij:i≠j) (c:ℂ) (hc:c≠0) :
    PairExchangeRegular (Function.update variableF i.castSucc (constF (n+1) c*variableF j.castSucc)) i j := by
  let E:Fin n → Fin (n+1) → ℤ:=fun a =>if a=i then variableExponent j.castSucc else variableExponent a.castSucc
  let C:Fin n → ℂ:=fun a =>if a=i then c else 1
  have he (a:Fin n):(Function.update variableF i.castSucc (constF (n+1) c*variableF j.castSucc)) a.castSucc=
      evalLaurent (monomialL (E a) (C a)) := by
    by_cases ha:a=i
    · subst a; simp only [Function.update_self,E,C,ite_true]
      change constF (n+1) c*evalLaurent (monomialL (variableExponent j.castSucc) 1)=_
      simpa using constF_mul_monomial c 1 (variableExponent j.castSucc)
    · simp only [Function.update_of_ne (fun h =>ha (Fin.castSucc_injective n h)),E,C,ite_eq_right ha]
      rfl
  have hC (a:Fin n):C a≠0 := by dsimp [C]; split_ifs <;> simp_all
  intro a b hab hpair
  rw [he,he]
  apply monomial_ratio_regular _ _ _ _ _ (hC b) (hC a)
  intro h
  by_cases hai:a=i <;> by_cases hbi:b=i
  · exact hab (hai.trans hbi.symm)
  · have hh: b=j := Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h))
    exact hpair (Or.inl ⟨hai,hh⟩)
  · have hh: a=j := Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h.symm))
    exact hpair (Or.inr ⟨hh,hbi⟩)
  · exact hab (Fin.castSucc_injective n (variableExponent_injective (by simpa [E,hai,hbi] using h.symm)))


 

 


lemma torusEvaluation_signLaurent {n m:ℕ} (i:Fin (n+1))
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (f:Laurent (n+1)) :
    torusEvaluation z hz (signLaurent i f)=
      torusEvaluation (Function.update z i (-z i))
        (fun j =>by by_cases h:j=i <;> simp [h,hz]) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,hf,hg]
  | single e c =>
    change torusEvaluation z hz (signLaurent i (monomialL e c))=
      torusEvaluation (Function.update z i (-z i)) _ (monomialL e c)
    rw [signLaurent_monomial,torusEvaluation_monomial,torusEvaluation_monomial]
    rw [Fin.prod_univ_succAbove _ i,Fin.prod_univ_succAbove _ i]
    simp only [Function.update_self,Function.update_of_ne (Fin.succAbove_ne i _),constF,map_mul,map_zpow₀,map_neg,map_one]
    rw [show -z i=(-1)*z i by ring,mul_zpow]
    ring

lemma torusEvaluation_neg_zero {n m:ℕ} (i:Fin (n+1))
    (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0) (f:Laurent (n+1))
    (hodd:signLaurent i f= -f) (h:torusEvaluation z hz f=0) :
    torusEvaluation (Function.update z i (-z i))
      (fun j =>by by_cases h:j=i <;> simp [h,hz]) f=0 := by
  rw [←torusEvaluation_signLaurent i z hz f,hodd,map_neg,h,neg_zero]


 

 


lemma lastEvaluation_residual_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (y:SpectralField n) (hy:y≠0)
    (hA:torusCos (y^2/constF n phase^3)=deletionBeta i) (p:Pairing (n+1)) :
    lastEvaluation y hy (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let φ:=lastEvaluation y hy
  have hpoly:=RationalAt.eval₂ φ.toRingHom (liftSpectral n) (RingHom.id _)
    (rationalAt_last_lift y hy) (rationalAt_last_spectralA y hy)
    (rationalResidualPolynomial n p)
  rw [Polynomial.eval₂_id,hA,rationalResidualPolynomial_at_node] at hpoly
  have hs:RationalAt φ.toRingHom
      (if p.Occupied (Fin.last n) then torusSin (variableF (Fin.last n)) else 1)
      (if p.Occupied (Fin.last n) then torusSin y else 1) := by
    split_ifs
    · exact rationalAt_torusSin φ (rationalAt_last_variable y hy) hy
    · exact RationalAt.one
  have hd:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    ((∏j:Fin n,rowDenominator j.castSucc) * algebraMap ℂ (Laurent (n+1)) (1/2))
  have hden:evalLaurent ((∏j:Fin n,rowDenominator j.castSucc) * algebraMap ℂ (Laurent (n+1)) (1/2))=
      (∏j:Fin n,evalLaurent (rowDenominator j.castSucc))/2 := by
    change evalLaurent ((∏j:Fin n,rowDenominator j.castSucc) * constantL (n+1) (1/2))=_
    simp only [evalLaurent,map_mul,map_prod,map_constantL]
    congr 1
    change (algebraMap ℂ (SpectralField (n+1))) (1/2)=(2:SpectralField (n+1))⁻¹
    norm_num
    rw [map_ofNat]
    norm_num
  change RationalAt _ (evalLaurent _) _ at hd
  rw [hden] at hd
  have hr:=hd.mul (hs.mul hpoly)
  simp only [mul_zero] at hr
  have he:=rationalInterpolationResidual_transfer (n:=n) p
  simp only [ite_mul,one_mul] at hr
  change RationalAt φ.toRingHom ((∏j:Fin n,evalLaurent (rowDenominator j.castSucc))/2 *
    lastValue (liftSpectral n) (spectralA (Fin.last n)) (torusSin (variableF (Fin.last n))) (rationalResidualPolynomial n) p) 0 at hr
  rw [←he] at hr
  have hf:=RationalAt.algebraMap (φ:=φ.toRingHom) (F:=SpectralField (n+1))
    (laurentResidual (fun q =>lastLaurent q (P q)) p)
  change RationalAt _ (evalLaurent _) _ at hf
  rw [laurentResidual_map P hP] at hf
  exact hf.unique hr

lemma residual_last_delete_universal {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzi:z (Fin.last n)=z i.castSucc*constF m phase^3) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let u:=monomialUnit (variableExponent i) (phase^3) (pow_ne_zero _ phase_ne_zero)
  have hu:evalLaurent (u:Laurent n)=deletionNode i := by
    simp [u,monomialUnit,evalLaurent_monomial_product,variableExponent,Pi.single_apply,deletionNode,constF,mul_comm]
  apply generic_substitution_zero (Fin.last n) u
    (Fin.snoc variableF (deletionNode i)) _ _ _ _
    (lastEvaluation_residual_zero P hP i _ (mul_ne_zero (variableF_ne_zero i) (pow_ne_zero _ (constF_phase_ne_zero n))) rfl p) z hz
  · simpa [u,monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF,mul_comm] using hzi
  · rw [Fin.snoc_last,hu]
  · intro j; simp

lemma residual_last_inverse_universal {n m:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (z:Fin (n+1) → SpectralField m) (hz:∀j,z j≠0)
    (hzi:z (Fin.last n)=(z i.castSucc)⁻¹) (p:Pairing (n+1)) :
    torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let u:=monomialUnit (-variableExponent i) 1 one_ne_zero
  have hu:evalLaurent (u:Laurent n)=(variableF i)⁻¹ := by
    simp [u,monomialUnit,evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF]
  have hA:torusCos (((variableF i)⁻¹)^2/constF n phase^3)=deletionBeta i := by
    rw [deletionBeta,deletionNode]
    have he:((variableF i)⁻¹)^2/constF n phase^3=
        ((variableF i*constF n phase^3)^2/constF n phase^3)⁻¹ := by
      field_simp [variableF_ne_zero,constF_phase_ne_zero]
    rw [he,torusCos_inv]
  apply generic_substitution_zero (Fin.last n) u
    (Fin.snoc variableF ((variableF i)⁻¹)) _ _ _ _
    (lastEvaluation_residual_zero P hP i _ (inv_ne_zero (variableF_ne_zero i)) hA p) z hz
  · simpa [u,monomialUnit,torusEvaluation_monomial,variableExponent,Pi.single_apply,constF] using hzi
  · rw [Fin.snoc_last,hu]
  · intro j; simp


 

 


def positiveResidualRoot {n:ℕ} (i:Fin n) (j:Fin (n+1)) (b:Bool) : SpectralField (n+1) :=
  if j=i.castSucc then (if b then constF (n+1) phase^3 else 1)
  else if j=Fin.last n then (if b then (variableF j)⁻¹ else (constF (n+1) phase^3)⁻¹*variableF j)
  else if j.val < i.val then constF (n+1) phase^(if b then 3 else 2)*variableF j
  else (constF (n+1) phase^(if b then 3 else 2))⁻¹*variableF j

lemma phase_more_powers :
    phase^10= -phase^2 ∧ phase^11= -phase^3 ∧ phase^13=(phase^3)⁻¹ ∧
    phase^14=(phase^2)⁻¹ ∧ phase^5= -(phase^3)⁻¹ ∧ phase^6= -(phase^2)⁻¹ := by
  have h16:phase^16=1 := by
    calc
      phase^16=(phase^8)^2 := by ring
      _=1 := by rw [phase_eight]; norm_num
  have h13:phase^13=(phase^3)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      phase^13*phase^3=phase^16 := by ring
      _=1 := h16
  have h14:phase^14=(phase^2)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    calc
      phase^14*phase^2=phase^16 := by ring
      _=1 := h16
  have h (k:ℕ):phase^(8+k)= -phase^k := by rw [pow_add,phase_eight,neg_one_mul]
  refine ⟨by simpa using h 2,by simpa using h 3,h13,h14,?_,?_⟩
  · have hh:=h 5; rw [show 8+5=13 from rfl,h13] at hh; linear_combination hh
  · have hh:=h 6; rw [show 8+6=14 from rfl,h14] at hh; linear_combination hh

lemma residualRoot_values {n:ℕ} (i:Fin n) (j:Fin (n+1)) (k:Fin 4) :
    residualRoot i (j,k)=
      if k=0 then positiveResidualRoot i j false else
      if k=1 then -positiveResidualRoot i j false else
      if k=2 then positiveResidualRoot i j true else -positiveResidualRoot i j true := by
  have hp:=phase_more_powers
  by_cases hi:j=i.castSucc
  · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,
      evalLaurent_monomial_product,constF,show evalLaurent (1:Laurent (n+1))=1 from map_one _,phase_eight,hp.2.1]
  · by_cases hl:j=Fin.last n
    · have hli : (Fin.last n : Fin (n+1))≠i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
      fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hl,hli,
        evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,phase_eight,
        hp.2.2.1,hp.2.2.2.2.1]
    · by_cases hji:j.val < i.val
      · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,hl,hji,
          evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,hp.1,hp.2.1]
      · fin_cases k <;> simp [residualRoot,residualRootPhase,residualRootExponent,positiveResidualRoot,hi,hl,hji,
          evalLaurent_monomial_product,variableExponent,Pi.single_apply,constF,
          hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1,hp.2.2.2.2.2]

lemma positiveResidualRoot_ne_zero {n:ℕ} (i:Fin n) (j:Fin (n+1)) (b:Bool) :
    positiveResidualRoot i j b≠0 := by
  cases b
  · simpa [residualRoot_values] using residualRoot_ne_zero i (j,0)
  · simpa [residualRoot_values] using residualRoot_ne_zero i (j,2)

lemma positiveRoot_negative_zero {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc)
    (j:Fin (n+1)) (b:Bool)
    (h:torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0) :
    torusEvaluation (Function.update variableF i.castSucc (-positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  have hh:=torusEvaluation_neg_zero i.castSucc _ _ _ (laurentResidual_odd P hP i p hp) h
  simpa only [Function.update_self,Function.update_idem] using hh

lemma residualRoot_signed {n:ℕ} (i:Fin n) (v:Fin (n+1) × Fin 4) :
    ∃b:Bool,residualRoot i v=positiveResidualRoot i v.1 b ∨
      residualRoot i v= -positiveResidualRoot i v.1 b := by
  rcases v with ⟨j,k⟩
  fin_cases k
  · exact ⟨false,Or.inl (by simp [residualRoot_values])⟩
  · exact ⟨false,Or.inr (by simp [residualRoot_values])⟩
  · exact ⟨true,Or.inl (by simp [residualRoot_values])⟩
  · exact ⟨true,Or.inr (by simp [residualRoot_values])⟩

lemma residual_root_grid_of_positive {n:ℕ}
    (P:Pairing (n+1) → Polynomial (Laurent n))
    (hP:∀p,(P p).map (algebraMap (SpectralRing n) (SpectralField n))=rationalNodalPolynomial n p)
    (i:Fin n) (p:Pairing (n+1)) (hp:p.Occupied i.castSucc)
    (hpos:∀j b,torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (v:Fin (n+1) × Fin 4) :
    torusEvaluation (Function.update variableF i.castSucc (residualRoot i v))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,residualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  obtain ⟨b,h|h⟩:=residualRoot_signed i v
  · simpa only [h] using hpos v.1 b
  · simpa only [h] using positiveRoot_negative_zero P hP i p hp v.1 b (hpos v.1 b)


 

 


lemma PairExchangeRegular.symm {n m:ℕ} {z:Fin (n+1) → SpectralField m} {i j:Fin n}
    (h:PairExchangeRegular z i j) : PairExchangeRegular z j i := by
  intro a b hab hij
  exact h a b hab (by tauto)

 

theorem residual_positive_roots {n:ℕ}
    (P:Pairing (n+2) → Polynomial (Laurent (n+1)))
    (hP:∀p,(P p).map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p)
    (hflat:∀(b:Bool) (z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z 0=(if b then constF (n+2) phase^3 else 1) → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (hpair:∀(h2:2≤n+1) (s:ℕ),s=2 ∨ s=3 →
      ∀(z:Fin (n+2) → SpectralField (n+2)) (hz:∀k,z k≠0),
      z (⟨1,by omega⟩:Fin (n+1)).castSucc=constF (n+2) phase^s*z (⟨0,by omega⟩:Fin (n+1)).castSucc → ∀p,
      torusEvaluation z hz (laurentResidual (fun q =>lastLaurent q (P q)) p)=0)
    (i:Fin (n+1)) (j:Fin (n+2)) (b:Bool) (p:Pairing (n+2)) :
    torusEvaluation (Function.update variableF i.castSucc (positiveResidualRoot i j b))
      (fun k =>by by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero])
      (laurentResidual (fun q =>lastLaurent q (P q)) p)=0 := by
  let z:=Function.update variableF i.castSucc (positiveResidualRoot i j b)
  have hz:∀k,z k≠0 := fun k =>by dsimp [z]; by_cases h:k=i.castSucc <;> simp [h,positiveResidualRoot_ne_zero,variableF_ne_zero]
  change torusEvaluation z hz _=0
  by_cases hji:j=i.castSucc
  · have hroot:positiveResidualRoot i j b=(if b then constF (n+2) phase^3 else 1) := by simp [positiveResidualRoot,hji]
    apply residual_flat_transport P hP _ (hflat b) i z hz
    · simp [z,hroot]
    · intro a ha
      cases b
      · simpa only [z,hroot,Bool.false_eq_true,ite_false,show constF (n+2) (1:ℂ)=1 from map_one (algebraMap ℂ _)] using
          flat_update_regular i a (Ne.symm (Fin.ne_of_lt ha)) 1 one_ne_zero
      · simpa only [z,hroot,ite_true,constF,map_pow] using
          flat_update_regular i a (Ne.symm (Fin.ne_of_lt ha)) (phase^3) (pow_ne_zero _ phase_ne_zero)
  · by_cases hjlast:j=Fin.last (n+1)
    · have hilast:(Fin.last (n+1):Fin (n+2))≠i.castSucc := Ne.symm (Fin.castSucc_ne_last i)
      cases b
      · apply residual_last_delete_universal P hP i z hz
        simp only [z,positiveResidualRoot,hjlast,hilast,ite_false,ite_true,Function.update_self,Function.update_of_ne hilast,Bool.false_eq_true]
        field_simp [constF_phase_ne_zero]
      · apply residual_last_inverse_universal P hP i z hz
        simp [z,positiveResidualRoot,hjlast,hilast]
    · obtain ⟨a,ha⟩:∃a:Fin (n+1),a.castSucc=j := by
        have hjv : j.val < n+1 := by
          have hne : j.val ≠ n+1 := by
            intro h
            apply hjlast
            exact Fin.ext h
          have := j.isLt
          omega
        exact ⟨⟨j.val,hjv⟩,rfl⟩
      subst j
      have hai:a≠i := fun h =>hji (congrArg Fin.castSucc h)
      let s:ℕ:=if b then 3 else 2
      have hs:s=2 ∨ s=3 := by cases b <;> simp [s]
      have h2:2≤n+1 := by have:=i.isLt; have:=a.isLt; have hne:i.val≠a.val := fun h =>hai (Fin.ext h.symm); omega
      by_cases hlt:a < i
      · have hroot:positiveResidualRoot i a.castSucc b=constF (n+2) phase^s*variableF a.castSucc := by
          simp [positiveResidualRoot,hji,hjlast,show a.val < i.val from hlt,s]
        have hr:PairExchangeRegular z i a := by
          simpa only [z,hroot,constF,map_pow] using pair_update_regular i a hai.symm (phase^s) (pow_ne_zero _ phase_ne_zero)
        apply residual_pair_transport P hP _ h2 (hpair h2 s hs) a i hlt z hz _ hr.symm p
        simp only [z,Function.update_self,Function.update_of_ne (fun h =>hai (Fin.castSucc_injective (n+1) h)),hroot]
      · have hia:i < a := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hai)
        have hroot:positiveResidualRoot i a.castSucc b=(constF (n+2) phase^s)⁻¹*variableF a.castSucc := by
          simp [positiveResidualRoot,hji,hjlast,show ¬a.val < i.val from hlt,s]
        have hr:PairExchangeRegular z i a := by
          simpa only [z,hroot,constF,map_inv₀,map_pow] using pair_update_regular i a hai.symm (phase^s)⁻¹ (inv_ne_zero (pow_ne_zero _ phase_ne_zero))
        apply residual_pair_transport P hP _ h2 (hpair h2 s hs) i a hia z hz _ hr p
        simp only [z,Function.update_self,Function.update_of_ne (fun h =>hai (Fin.castSucc_injective (n+1) h)),hroot]
        field_simp [constF_phase_ne_zero]

end
end CriticalStrip.Diagram

end OAI
