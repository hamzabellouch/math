import Mathlib
import OAI.Combinatorics.StripMass.NodalExchange
import OAI.Combinatorics.StripMass.Specialization

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open scoped LaurentPolynomial Classical

lemma cosineCollisionPacket_eval_root {R : Type*} [CommRing R] [IsDomain R]
    (a u : Rˣ) (k : Fin 4) :
    LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k) (cosineCollisionPacket a u)=0 := by
  let φ:=LaurentPolynomial.eval₂ (RingHom.id R) (cosineCollisionRoots a u k)
  have h:=congrArg φ (cosineCollision_factorization a u)
  rw [map_mul,map_prod] at h
  have hz : (∏ l : Fin 4,φ (LaurentPolynomial.T 1-LaurentPolynomial.C ((cosineCollisionRoots a u l):R)))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (by simp [φ,laurent_eval_linear])
  rw [hz] at h
  apply (mul_eq_zero.mp h.symm).resolve_left
  simp only [φ,map_mul,LaurentPolynomial.eval₂_C,LaurentPolynomial.eval₂_T,RingHom.id_apply,
    zpow_ofNat]
  exact mul_ne_zero (Units.ne_zero _) (pow_ne_zero _ (Units.ne_zero _))

def collisionCopy {n : ℕ} (i : Fin (n+1)) (j : Fin n) : Fin (n+1) → Fin n := Fin.insertNth i j id

def collisionSubstitution {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) :
    Laurent (n+1) →+* Laurent n :=
  substituteLaurent i (cosineCollisionRoots
    (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k)

lemma collisionSubstitution_beta_self {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) :
    collisionSubstitution i j k (betaL i)=betaL j := by
  have h:=cosineCollisionPacket_eval_root
    (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k
  rw [cosineCollisionPacket_betaL i j,map_mul,map_ofNat] at h
  have hzero : collisionSubstitution i j k (betaL i-betaL (i.succAbove j))=0 := by
    exact (mul_eq_zero.mp h).resolve_left (by
      intro hz
      have h:=congrArg (algebraMap (SpectralRing n) (SpectralField n)) hz
      simp only [map_ofNat,map_zero] at h
      exact (two_ne_zero : (2 : SpectralField n)≠0) h)
  rw [map_sub] at hzero
  have ho : collisionSubstitution i j k (betaL (i.succAbove j))=betaL j := by
    rw [←insert_betaL i j]
    exact substituteLaurent_insert _ _ _
  rw [ho] at hzero
  exact sub_eq_zero.mp hzero

lemma collisionSubstitution_beta {n : ℕ} (i : Fin (n+1)) (j : Fin n) (k : Fin 4) (l : Fin (n+1)) :
    collisionSubstitution i j k (betaL l)=betaL (collisionCopy i j l) := by
  refine Fin.succAboveCases i ?_ (fun l => ?_) l
  · simpa only [collisionCopy,Fin.insertNth_apply_same] using collisionSubstitution_beta_self i j k
  · simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]
    rw [←insert_betaL i l]
    exact substituteLaurent_insert _ _ _

lemma collisionCopy_eq {n : ℕ} (i : Fin (n+1)) (j : Fin n) (r s : Fin (n+1)) (hrs:r≠s)
    (h:collisionCopy i j r=collisionCopy i j s) :
    (r=i ∧ s=i.succAbove j) ∨ (r=i.succAbove j ∧ s=i) := by
  unfold collisionCopy at h
  revert h hrs
  refine Fin.succAboveCases i ?_ (fun r => ?_) r
  · refine Fin.succAboveCases i ?_ (fun s => ?_) s
    · intro hrs _; exact (hrs rfl).elim
    · intro _ h
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq] at h
      exact Or.inl ⟨rfl,congrArg i.succAbove h.symm⟩
  · refine Fin.succAboveCases i ?_ (fun s => ?_) s
    · intro _ h
      simp only [Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq] at h
      exact Or.inr ⟨congrArg i.succAbove h,rfl⟩
    · intro hrs h
      simp only [Fin.insertNth_apply_succAbove,id_eq] at h
      exact (hrs (congrArg i.succAbove h)).elim

lemma collisionSubstitution_cross {n : ℕ} (i : Fin (n+1)) (j : Fin n)
    (hij : i < i.succAbove j) (e:UpperPair (n+1)) (hne:e≠⟨(i,i.succAbove j),hij⟩) (k : Fin 4) :
    collisionSubstitution i j k (betaL e.val.1-betaL e.val.2)≠0 := by
  rw [map_sub,collisionSubstitution_beta,collisionSubstitution_beta]
  apply sub_ne_zero.mpr
  intro h
  have hcopy:=cosineL_two_injective _ (pow_ne_zero 3 phase_ne_zero) h
  rcases collisionCopy_eq i j e.val.1 e.val.2 (ne_of_lt e.property) hcopy with h | h
  · apply hne
    exact Subtype.ext (Prod.ext h.1 h.2)
  · have he:=e.property
    rw [h.1,h.2] at he
    exact lt_asymm hij he

end

 

 

noncomputable section
open scoped Classical

lemma copyEvaluation_collision {n : ℕ} (i : Fin (n+1)) (j : Fin n) (f : Laurent (n+1)) :
    copyEvaluation (collisionCopy i j) f=evalLaurent (substituteLaurent i (variableUnit j) f) := by
  apply substitution_torusEvaluation
  · simp only [collisionCopy,Fin.insertNth_apply_same]
    rfl
  · intro k
    simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]

lemma nodalDatumL_copy_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    copyEvaluation (collisionCopy i j) (nodalDatumL W i p)=
      copyEvaluation (collisionCopy i j) (nodalDatumL W (i.succAbove j) p) := by
  have hij:collisionCopy i j i=collisionCopy i j (i.succAbove j) := by
    simp only [collisionCopy,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,id_eq]
  have hm (k : Fin (n+1)) :
      RationalAt (copyEvaluation (collisionCopy i j)).toRingHom
        (nodalVacuum k p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode k) else 1))
        (copyEvaluation (collisionCopy i j) (nodalDatumL W k p)) := by
    rw [←nodalDatumL_map W hW k p]
    exact RationalAt.algebraMap _
  by_cases hp:p.Occupied (Fin.last (n+1))
  · obtain ⟨y,hy,hz⟩:=occupied_nodal_collision (collisionCopy i j) i (i.succAbove j) hij p
    have hmi:=hm i
    have hmj:=hm (i.succAbove j)
    simp only [hp,ite_true] at hmi hmj
    exact (hmi.unique hy).trans (hmj.unique hz).symm
  · obtain ⟨y,hy,hz⟩:=nodalVacuum_collision (collisionCopy i j) i (i.succAbove j) hij p
    have hmi:=hm i
    have hmj:=hm (i.succAbove j)
    simp only [hp,ite_false,div_one] at hmi hmj
    exact (hmi.unique hy).trans (hmj.unique hz).symm

lemma nodalDatumL_ordinary_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    substituteLaurent i (variableUnit j) (nodalDatumL W i p)=
      substituteLaurent i (variableUnit j) (nodalDatumL W (i.succAbove j) p) := by
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  exact (copyEvaluation_collision i j _).symm.trans
    ((nodalDatumL_copy_collision W hW i j p).trans (copyEvaluation_collision i j _))


 

 


def reflectionUnit {n : ℕ} (j : Fin n) : (Laurent n)ˣ :=
  (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))⁻¹*(variableUnit j)⁻¹

@[simp] lemma reflectionUnit_coe {n : ℕ} (j : Fin n) :
    (reflectionUnit j : Laurent n)=monomialL (-variableExponent j) ((phase^3)⁻¹) := by
  simp only [reflectionUnit,Units.val_mul,constantUnit_inv_coe,variableUnit_inv_coe,
    monomialL_mul,zero_add,mul_one]

@[simp] lemma reflectionUnit_inv_coe {n : ℕ} (j : Fin n) :
    ((reflectionUnit j)⁻¹ : (Laurent n)ˣ).val=monomialL (variableExponent j) (phase^3) := by
  simp only [reflectionUnit,mul_inv_rev,inv_inv,Units.val_mul,constantUnit_coe,variableUnit_coe,
    monomialL_mul,add_zero,one_mul]

lemma substitute_reflection_sine {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j)
      (sineL (variableExponent i+variableExponent (i.succAbove j)) (phase^3))=0 := by
  have hrem : Fin.removeNth i (variableExponent i+variableExponent (i.succAbove j))=variableExponent j := by
    funext k
    simp [Fin.removeNth,variableExponent,Pi.single_apply,Fin.succAbove_ne]
  have he : (variableExponent i+variableExponent (i.succAbove j)) i=1 := by
    simp [variableExponent,(Fin.succAbove_ne i j).symm]
  have hremn : Fin.removeNth i (-(variableExponent i+variableExponent (i.succAbove j)))= -variableExponent j := by
    funext k
    change -(Fin.removeNth i (variableExponent i+variableExponent (i.succAbove j)) k)=_
    rw [hrem]; rfl
  rw [sineL,map_mul]
  suffices h : substituteLaurent i (reflectionUnit j)
      (monomialL (variableExponent i+variableExponent (i.succAbove j)) (phase^3) -
       monomialL (-(variableExponent i+variableExponent (i.succAbove j))) ((phase^3)⁻¹))=0 by
    rw [h,zero_mul]
  rw [map_sub,substituteLaurent_monomial,substituteLaurent_monomial]
  simp only [hrem,hremn,he,Pi.neg_apply,zpow_one,zpow_neg_one,reflectionUnit_coe,
    reflectionUnit_inv_coe,monomialL_mul,add_neg_cancel,neg_add_cancel]
  apply sub_eq_zero.mpr
  congr 1
  field_simp [phase_ne_zero]

lemma reflectionFactorL_collision_left {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j) (reflectionFactorL i (i.succAbove j))=0 := by
  rw [reflectionFactorL,ite_eq_right (Fin.succAbove_ne i j)]
  exact substitute_reflection_sine i j

lemma reflectionFactorL_collision_right {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    substituteLaurent i (reflectionUnit j) (reflectionFactorL (i.succAbove j) i)=0 := by
  rw [reflectionFactorL,ite_eq_right (Fin.succAbove_ne i j).symm,
    add_comm (variableExponent (i.succAbove j)) (variableExponent i)]
  exact substitute_reflection_sine i j

lemma nodalDatumL_reflection {n : ℕ} (W : Pairing n → Laurent n)
    (i : Fin (n+1)) (j : Fin n) (p : Pairing (n+2)) :
    substituteLaurent i (reflectionUnit j) (nodalDatumL W i p)=0 ∧
      substituteLaurent i (reflectionUnit j) (nodalDatumL W (i.succAbove j) p)=0 := by
  have h1 : (∏ l:Fin (n+1),substituteLaurent i (reflectionUnit j) (reflectionFactorL i l))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ (i.succAbove j)) (reflectionFactorL_collision_left i j)
  have h2 : (∏ l:Fin (n+1),substituteLaurent i (reflectionUnit j) (reflectionFactorL (i.succAbove j) l))=0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (reflectionFactorL_collision_right i j)
  simp only [nodalDatumL,map_mul,map_prod,h1,h2,zero_mul,and_self]


 

 


lemma substituteLaurent_neg_sign_monomial {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ)
    (e : Fin (n+1) → ℤ) (z : ℂ) :
    substituteLaurent i (-u) (monomialL e z)=substituteLaurent i u (signLaurent i (monomialL e z)) := by
  rw [signLaurent_monomial,substituteLaurent_monomial,substituteLaurent_monomial]
  apply IsFractionRing.injective (SpectralRing n) (SpectralField n)
  change evalLaurent (_ * _)=evalLaurent (_ * _)
  simp only [evalLaurent,map_mul]
  rw [←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow,
    ←evalLaurent,evalLaurent_monomial_product,←evalLaurent,evalLaurent_unit_zpow]
  simp only [Units.val_neg,evalLaurent,map_neg,constF,map_mul,map_zpow₀,map_neg,map_one]
  rw [neg_eq_neg_one_mul,mul_zpow]
  ring

lemma substituteLaurent_neg_sign {n : ℕ} (i : Fin (n+1)) (u : (Laurent n)ˣ) (f:Laurent (n+1)) :
    substituteLaurent i (-u) f=substituteLaurent i u (signLaurent i f) := by
  have h:(substituteLaurent i (-u))=(substituteLaurent i u).comp (signLaurent i) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro z
      exact substituteLaurent_neg_sign_monomial i u 0 z
    · intro e
      exact substituteLaurent_neg_sign_monomial i u e 1
  exact DFunLike.congr_fun h f


 

 


lemma nodalDatumL_collision {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n)
    (p : Pairing (n+2)) (k : Fin 4) :
    collisionSubstitution i j k (nodalDatumL W i p)=
      collisionSubstitution i j k (nodalDatumL W (i.succAbove j) p) := by
  have ho:=nodalDatumL_ordinary_collision W hW i j p
  have hr:=nodalDatumL_reflection W i j p
  fin_cases k
  · exact ho
  · change substituteLaurent i (-(variableUnit j)) _=substituteLaurent i (-(variableUnit j)) _
    rw [substituteLaurent_neg_sign,substituteLaurent_neg_sign,
      nodalDatumL_sign W hW,nodalDatumL_sign W hW]
    split_ifs <;> simp only [map_neg,ho]
  · exact hr.1.trans hr.2.symm
  · change substituteLaurent i (-(reflectionUnit j)) _=substituteLaurent i (-(reflectionUnit j)) _
    rw [substituteLaurent_neg_sign,substituteLaurent_neg_sign,
      nodalDatumL_sign W hW,nodalDatumL_sign W hW]
    split_ifs <;> simp only [map_neg,hr.1,hr.2]

lemma interpolationNumerator_collisionSubstitution {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (i : Fin (n+1)) (j : Fin n)
    (p : Pairing (n+2)) (k : Fin 4) (a : Fin (n+1)) :
    collisionSubstitution i j k
      (interpolationNumerator betaL (fun l => nodalDatumL W l p) a)=0 := by
  rw [interpolationNumerator_map]
  apply interpolationNumerator_collision _ _ i (i.succAbove j) (Fin.succAbove_ne i j).symm
  · rw [collisionSubstitution_beta_self,collisionSubstitution_beta]
    simp only [collisionCopy,Fin.insertNth_apply_succAbove,id_eq]
  · exact nodalDatumL_collision W hW i j p k


 

 


def upperPairOther {n : ℕ} (e : UpperPair (n+1)) : Fin n :=
  (Fin.exists_succAbove_eq (ne_of_gt e.property)).choose

lemma upperPairOther_spec {n : ℕ} (e : UpperPair (n+1)) :
    e.val.1.succAbove (upperPairOther e)=e.val.2 :=
  (Fin.exists_succAbove_eq (ne_of_gt e.property)).choose_spec

def edgeSubstitution {n : ℕ} (e : UpperPair (n+1)) (k : Fin 4) :
    Laurent (n+1) →+* Laurent n := collisionSubstitution e.val.1 (upperPairOther e) k

lemma edgeSubstitution_kernel {n : ℕ} (e : UpperPair (n+1)) (f : Laurent (n+1))
    (hf:∀ k,edgeSubstitution e k f=0) : (betaL e.val.2-betaL e.val.1) ∣ f := by
  obtain ⟨g,hg⟩:=betaL_difference_dvd e.val.1 (upperPairOther e) f hf
  rw [upperPairOther_spec] at hg
  refine ⟨-g,?_⟩
  rw [hg]
  ring

lemma edgeSubstitution_cross {n : ℕ} (e f : UpperPair (n+1)) (hef:e≠f) (k : Fin 4) :
    edgeSubstitution e k (betaL f.val.2-betaL f.val.1)≠0 := by
  have he:e.val.1<e.val.1.succAbove (upperPairOther e) := by rw [upperPairOther_spec]; exact e.property
  have hne:f≠⟨(e.val.1,e.val.1.succAbove (upperPairOther e)),he⟩ := by
    intro hh
    apply hef
    apply Subtype.ext
    have hv:=congrArg Subtype.val hh
    simpa only [upperPairOther_spec] using hv.symm
  have hh:=collisionSubstitution_cross e.val.1 (upperPairOther e) he f hne k
  intro hz
  rw [map_sub] at hh hz
  exact hh (sub_eq_zero.mpr (sub_eq_zero.mp hz).symm)

 

theorem nodal_vandermonde_dvd {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (p : Pairing (n+2)) (a : Fin (n+1)) :
    (Matrix.vandermonde (@betaL (n+1))).det ∣
      interpolationNumerator betaL (fun l => nodalDatumL W l p) a := by
  rw [Matrix.det_vandermonde,←prod_upperPair]
  apply prod_dvd_of_evaluation_packets Finset.univ _ edgeSubstitution
  · intro e _ f hf
    exact edgeSubstitution_kernel e f hf
  · intro e _ f _ hef k
    exact edgeSubstitution_cross e f hef k
  · intro e _ k
    exact interpolationNumerator_collisionSubstitution W hW e.val.1 (upperPairOther e) p k a


 

 


 

lemma interpolate_lift_of_vandermonde_dvd {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) {n : ℕ} (b y : Fin n → R)
    (hb : Function.Injective (fun i => φ (b i)))
    (hd : ∀ k,(Matrix.vandermonde b).det ∣ interpolationNumerator b y k) :
    ∃ P : Polynomial R,P.map φ=Lagrange.interpolate Finset.univ (fun i => φ (b i)) (fun i => φ (y i)) := by
  choose q hq using hd
  let p:=Lagrange.interpolate Finset.univ (fun i => φ (b i)) (fun i => φ (y i))
  have hdet:φ (Matrix.vandermonde b).det=(Matrix.vandermonde (fun i => φ (b i))).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [Matrix.map_apply,Matrix.vandermonde_apply]
  have hc (k:Fin n):φ (q k)=p.coeff k := by
    have h:=congrArg φ (hq k)
    rw [interpolationNumerator_map,map_mul,hdet,
      interpolationNumerator_eq_det_mul_coeff _ _ hb] at h
    exact mul_left_cancel₀ (Matrix.det_vandermonde_ne_zero_iff.mpr hb) h.symm
  refine ⟨Polynomial.ofFn n q,?_⟩
  ext k
  rw [Polynomial.coeff_map]
  by_cases hk:k<n
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk]
    exact hc ⟨k,hk⟩
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),map_zero]
    symm
    apply Polynomial.coeff_eq_zero_of_degree_lt
    have hp:=Lagrange.degree_interpolate_lt (s:=Finset.univ) (fun i => φ (y i)) hb.injOn
    simp only [Finset.card_univ,Fintype.card_fin] at hp
    exact hp.trans_le (by exact_mod_cast (show n≤k by omega))

lemma nodalLow_laurent {n : ℕ} (W : Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p) (p : Pairing (n+2)) :
    ∃ P : Polynomial (Laurent (n+1)),P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      Lagrange.interpolate Finset.univ deletionBeta
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)) := by
  have hbmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (betaL i)=deletionBeta i := betaL_map i
  have hdmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (nodalDatumL W i p)=
      nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) := nodalDatumL_map W hW i p
  have hh:=interpolate_lift_of_vandermonde_dvd
    (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))
    betaL (fun i => nodalDatumL W i p)
    (by simpa only [hbmap] using deletionBeta_injective (n+1))
    (nodal_vandermonde_dvd W hW p)
  simpa only [hbmap,hdmap] using hh

lemma rationalNodalPolynomial_laurent {n : ℕ}
    (W : Pairing n → Laurent n) (V : Pairing (n+1) → Laurent (n+1))
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p)
    (hV:∀ p,evalLaurent (V p)=rationalVacuum (n+1) p) (p:Pairing (n+2)) :
    ∃ P : Polynomial (Laurent (n+1)),P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
      rationalNodalPolynomial (n+1) p := by
  obtain ⟨P,hP⟩:=nodalLow_laurent W hW p
  by_cases hp:p.Occupied (Fin.last (n+1))
  · refine ⟨P,?_⟩
    simpa only [rationalNodalPolynomial,hp,ite_true] using hP
  · refine ⟨Polynomial.C (V (p.restrict Fin.castSuccOrderEmb))*Lagrange.nodal Finset.univ betaL+P,?_⟩
    simp only [rationalNodalPolynomial,hp,ite_false,Polynomial.map_add,Polynomial.map_mul,
      Polynomial.map_C,hP,div_one]
    rw [show (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (V (p.restrict Fin.castSuccOrderEmb))=
      rationalVacuum (n+1) (p.restrict Fin.castSuccOrderEmb) from hV _]
    congr 2
    have hbmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (betaL i)=deletionBeta i := betaL_map i
    simp only [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
      Polynomial.map_C,hbmap]


 

 


def PolynomialBox {n:ℕ} (P:Polynomial (Laurent n)) (b:Fin n → ℕ) : Prop :=
  ∀ k,LaurentBox (P.coeff k) b

lemma PolynomialBox.mono {n:ℕ} {P:Polynomial (Laurent n)} {a b:Fin n → ℕ}
    (hP:PolynomialBox P a) (hab:∀ i,a i≤b i) : PolynomialBox P b := fun k => (hP k).mono hab
lemma PolynomialBox.zero {n:ℕ} (b:Fin n → ℕ) : PolynomialBox (0:Polynomial (Laurent n)) b := by
  intro k
  rw [Polynomial.coeff_zero]
  exact LaurentBox.zero _
lemma PolynomialBox.C {n:ℕ} {f:Laurent n} {b:Fin n → ℕ} (hf:LaurentBox f b) :
    PolynomialBox (Polynomial.C f) b := by
  intro k
  by_cases hk:k=0
  · subst k; simpa only [Polynomial.coeff_C_zero] using hf
  · rw [Polynomial.coeff_C,ite_eq_right hk]
    exact LaurentBox.zero _
lemma PolynomialBox.X {n:ℕ} : PolynomialBox (Polynomial.X:Polynomial (Laurent n)) 0 := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · exact LaurentBox.one
  · exact LaurentBox.zero _
lemma PolynomialBox.add {n:ℕ} {P Q:Polynomial (Laurent n)} {b:Fin n → ℕ}
    (hP:PolynomialBox P b) (hQ:PolynomialBox Q b) : PolynomialBox (P+Q) b := by
  intro k; rw [Polynomial.coeff_add]; exact (hP k).add (hQ k)
lemma PolynomialBox.sub {n:ℕ} {P Q:Polynomial (Laurent n)} {b:Fin n → ℕ}
    (hP:PolynomialBox P b) (hQ:PolynomialBox Q b) : PolynomialBox (P-Q) b := by
  intro k; rw [Polynomial.coeff_sub]; exact (hP k).sub (hQ k)
lemma PolynomialBox.mul {n:ℕ} {P Q:Polynomial (Laurent n)} {a b:Fin n → ℕ}
    (hP:PolynomialBox P a) (hQ:PolynomialBox Q b) : PolynomialBox (P*Q) (a+b) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact LaurentBox.sum _ _ _ (fun ij _ => (hP ij.1).mul (hQ ij.2))
lemma PolynomialBox.one {n:ℕ} : PolynomialBox (1:Polynomial (Laurent n)) 0 := by
  simpa only [Polynomial.C_1] using (PolynomialBox.C (n:=n) LaurentBox.one)
lemma PolynomialBox.prod {n:ℕ} {ι:Type*} (s:Finset ι) (P:ι → Polynomial (Laurent n))
    (b:ι → Fin n → ℕ) (h:∀ i∈s,PolynomialBox (P i) (b i)) :
    PolynomialBox (∏ i∈s,P i) (∑ i∈s,b i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty,Finset.sum_empty] using PolynomialBox.one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma nodalLow_laurent_box {n:ℕ} (W:Pairing n → Laurent n)
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p)
    (hb:∀ p,LaurentBox (W p) (fun _ => 2*n-2)) (p:Pairing (n+2)) :
    ∃ P:Polynomial (Laurent (n+1)),
      P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=
        Lagrange.interpolate Finset.univ deletionBeta
          (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1)) ∧
      PolynomialBox P (fun _ => 2*n+2) := by
  let φ:=algebraMap (SpectralRing (n+1)) (SpectralField (n+1))
  obtain ⟨P,hP⟩:=nodalLow_laurent W hW p
  refine ⟨P,hP,?_⟩
  intro a
  have hcoef:φ (P.coeff a)=
      (Lagrange.interpolate Finset.univ deletionBeta
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))).coeff a := by
    rw [←hP,Polynomial.coeff_map]
  by_cases ha:a<n+1
  · have he:interpolationNumerator betaL (fun i => nodalDatumL W i p) ⟨a,ha⟩=
        (Matrix.vandermonde (@betaL (n+1))).det*P.coeff a := by
      apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
      rw [map_mul,hcoef,interpolationNumerator_map,RingHom.map_det]
      have hbmap (i:Fin (n+1)):φ (betaL i)=deletionBeta i := betaL_map i
      have hdmap (i:Fin (n+1)):φ (nodalDatumL W i p)=
          nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1) :=
        nodalDatumL_map W hW i p
      change interpolationNumerator (fun i => φ (betaL i)) (fun i => φ (nodalDatumL W i p)) ⟨a,ha⟩=_
      simp only [hbmap,hdmap]
      rw [interpolationNumerator_eq_det_mul_coeff _ _ (deletionBeta_injective (n+1))]
      congr 2
      ext i j
      change deletionBeta i ^ j.val=φ (betaL i ^ j.val)
      rw [map_pow,hbmap]
    apply LaurentBox.of_peel
    intro k
    have hn:LaurentInterval (peelLaurent k (P.coeff a)*peelLaurent k (Matrix.vandermonde (@betaL (n+1))).det)
        (-(4*n+2:ℤ)) (4*n+2) := by
      have hh:=(interpolationNumerator_box W hb p ⟨a,ha⟩).peel k
      rw [he,map_mul,mul_comm] at hh
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
    obtain ⟨hg,hlo,hhi⟩:=vandermonde_beta_exact k
    have hq:=hn.quotient hg hlo hhi
    convert hq using 1 <;> push_cast <;> ring
  · have he:P.coeff a=0 := by
      apply IsFractionRing.injective (SpectralRing (n+1)) (SpectralField (n+1))
      rw [hcoef,map_zero]
      apply Polynomial.coeff_eq_zero_of_degree_lt
      have hh:=Lagrange.degree_interpolate_lt (s:=Finset.univ)
        (fun i => nodalVacuum i p/(if p.Occupied (Fin.last (n+1)) then torusSin (deletionNode i) else 1))
        (deletionBeta_injective (n+1)).injOn
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      exact hh.trans_le (by exact_mod_cast (show n+1≤a by omega))
    rw [he]
    exact LaurentBox.zero _

end

 

 

noncomputable section
open scoped Classical

lemma nodal_betaL_box {n:ℕ} : PolynomialBox (Lagrange.nodal Finset.univ (@betaL n)) (fun _ => 2) := by
  unfold Lagrange.nodal
  have h:=PolynomialBox.prod Finset.univ
    (fun i:Fin n => Polynomial.X-Polynomial.C (betaL i)) (fun i => selfBound i 2)
    (fun i _ => (PolynomialBox.X.mono (fun k => Nat.zero_le _)).sub (PolynomialBox.C (betaL_box i)))
  convert h using 1
  funext k
  simp only [Finset.sum_apply,selfBound,Finset.sum_ite_eq,Finset.mem_univ,ite_true]

 

lemma rationalNodalPolynomial_laurent_box {n:ℕ}
    (W:Pairing n → Laurent n) (V:Pairing (n+1) → Laurent (n+1))
    (hW:∀ p,evalLaurent (W p)=rationalVacuum n p)
    (hV:∀ p,evalLaurent (V p)=rationalVacuum (n+1) p)
    (bW:∀ p,LaurentBox (W p) (fun _ => 2*n-2))
    (bV:∀ p,LaurentBox (V p) (fun _ => 2*n)) (p:Pairing (n+2)) :
    ∃ P:Polynomial (Laurent (n+1)),
      P.map (algebraMap (SpectralRing (n+1)) (SpectralField (n+1)))=rationalNodalPolynomial (n+1) p ∧
      PolynomialBox P (fun _ => 2*n+2) := by
  obtain ⟨P,hP,bP⟩:=nodalLow_laurent_box W hW bW p
  by_cases hp:p.Occupied (Fin.last (n+1))
  · refine ⟨P,?_,bP⟩
    simpa only [rationalNodalPolynomial,hp,ite_true] using hP
  · refine ⟨Polynomial.C (V (p.restrict Fin.castSuccOrderEmb))*Lagrange.nodal Finset.univ betaL+P,?_,?_⟩
    · simp only [rationalNodalPolynomial,hp,ite_false,Polynomial.map_add,Polynomial.map_mul,
        Polynomial.map_C,hP,div_one]
      rw [show (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (V (p.restrict Fin.castSuccOrderEmb))=
        rationalVacuum (n+1) (p.restrict Fin.castSuccOrderEmb) from hV _]
      congr 2
      have hbmap (i:Fin (n+1)) : (algebraMap (SpectralRing (n+1)) (SpectralField (n+1))) (betaL i)=deletionBeta i := betaL_map i
      simp only [Lagrange.nodal,Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,
        Polynomial.map_C,hbmap]
    · exact ((PolynomialBox.C (bV _)).mul nodal_betaL_box).add bP

end
end CriticalStrip.Diagram

end OAI
