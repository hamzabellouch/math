import Mathlib
import OAI.Combinatorics.StripMass.FirstFlatSpecialization

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section
open Finset

theorem cosine_difference_degree_self {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.degreeOf i (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) = 1 := by
  have hlt : MvPolynomial.degreeOf i (-MvPolynomial.X j : CosineRing n) <
      MvPolynomial.degreeOf i (MvPolynomial.X i : CosineRing n) := by
    simp [MvPolynomial.degreeOf_X, hij]
  simpa only [sub_eq_add_neg, MvPolynomial.degreeOf_X_self] using
    MvPolynomial.degreeOf_add_eq_of_degreeOf_lt hlt

theorem cosine_difference_degree {n : ℕ} (k i j : Fin n) (hij : i ≠ j) :
    MvPolynomial.degreeOf k (MvPolynomial.X i - MvPolynomial.X j : CosineRing n) =
      if i = k ∨ j = k then 1 else 0 := by
  by_cases hi : i = k
  · subst i
    simp [cosine_difference_degree_self k j hij]
  · by_cases hj : j = k
    · subst j
      have he : (MvPolynomial.X i - MvPolynomial.X k : CosineRing n) =
          -(MvPolynomial.X k - MvPolynomial.X i) := by ring
      rw [he, MvPolynomial.degreeOf_neg, cosine_difference_degree_self k i hij.symm]
      simp
    · rw [ite_eq_right (not_or.mpr ⟨hi,hj⟩)]
      apply Nat.eq_zero_of_le_zero
      exact (MvPolynomial.degreeOf_sub_le _ _ _).trans (by
        simp [MvPolynomial.degreeOf_X, Ne.symm hi, Ne.symm hj])

theorem sourceVandermonde_degree {n : ℕ} (k : Fin n) :
    MvPolynomial.degreeOf k (sourceVandermonde (MvPolynomial.X : Fin n → CosineRing n)) = n-1 := by
  unfold sourceVandermonde
  rw [MvPolynomial.degreeOf_prod_eq _ _ (fun e _ =>
    (prime_cosine_difference e.val.1 e.val.2 (ne_of_lt e.property)).ne_zero)]
  calc
    _ = ∑ e : UpperPair n, if e.val.1 = k ∨ e.val.2 = k then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact cosine_difference_degree k e.val.1 e.val.2 (ne_of_lt e.property)
    _ = n-1 := by simpa using sum_incident_degree k 1

 

theorem scalarPolynomial_degree (n : ℕ) (dd rr : ℂ) (hdd : dd ≠ 0) (k : Fin n) :
    MvPolynomial.degreeOf k (scalarPolynomial n dd rr hdd) ≤ n-1 := by
  by_cases hp : scalarPolynomial n dd rr hdd = 0
  · simp [hp]
  have hv := sourceVandermonde_ne_zero (MvPolynomial.X : Fin n → CosineRing n)
    MvPolynomial.X_injective
  have hd := scalarNumerator_degree n dd rr k
  rw [scalarNumerator_eq_vandermonde n dd rr hdd, MvPolynomial.degreeOf_mul_eq hv hp,
    sourceVandermonde_degree] at hd
  omega

end

 

 

noncomputable section
open scoped Classical

 

def firstScalarHom {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ} (a:Fin n → K) :
    CosineRing (n+1) →+* Polynomial K :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp f) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)))

lemma firstScalarHom_degree {K:Type*} [CommRing K] (f:ℂ →+* K) {n:ℕ}
    (a:Fin n → K) (P:CosineRing (n+1)) :
    (firstScalarHom f a P).natDegree ≤ MvPolynomial.degreeOf 0 P := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have he:firstScalarHom f a (MvPolynomial.monomial m (P.coeff m))=
      Polynomial.C (f (P.coeff m))*Polynomial.X^(m 0)*
        ∏ i:Fin n,Polynomial.C (a i)^(m i.succ) := by
    simp only [firstScalarHom,MvPolynomial.eval₂Hom_monomial,RingHom.comp_apply]
    rw [Finsupp.prod_fintype _ _ (by simp),Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,mul_assoc]
  rw [he]
  have hz:(∏i:Fin n,Polynomial.C (a i)^(m i.succ)).natDegree=0 := by
    have hh:(∏i:Fin n,Polynomial.C (a i)^(m i.succ))=Polynomial.C (∏i:Fin n,(a i)^(m i.succ)) := by
      simp only [map_prod,map_pow]
    rw [hh,Polynomial.natDegree_C]
  exact (Polynomial.natDegree_mul_le.trans (by
    rw [hz,add_zero]
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow_le _))) |>.trans
      (MvPolynomial.le_degreeOf_of_mem_support 0 hm)

lemma scalarPolynomial_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).natDegree ≤ n := by
  exact (firstScalarHom_degree f a _).trans (by simpa using scalarPolynomial_degree (n+1) dd rr hdd 0)

lemma polynomial_top_numerator {K:Type*} [CommRing K] (rr a:K) :
    ((Polynomial.X-Polynomial.C a)*(Polynomial.X+Polynomial.C a+Polynomial.C rr)).coeff 2=1 := by
  have he:(Polynomial.X-Polynomial.C a)*(Polynomial.X+Polynomial.C a+Polynomial.C rr)=
      (Polynomial.X^2:Polynomial K)+Polynomial.C rr*Polynomial.X-Polynomial.C (a*(a+rr)) := by
    simp only [map_mul,map_add]; ring
  rw [he]; simp

lemma polynomial_top_discriminant {K:Type*} [CommRing K] (dd a:K) :
    (discriminant (Polynomial.C dd) Polynomial.X (Polynomial.C a)).coeff 2=1 := by
  have he:discriminant (Polynomial.C dd) Polynomial.X (Polynomial.C a)=
      (Polynomial.X^2:Polynomial K)+Polynomial.C (2*dd*a)*Polynomial.X+Polynomial.C (a^2-dd^2) := by
    simp only [discriminant,map_mul,map_pow,map_sub,map_ofNat]; ring
  rw [he]
  have hc (z:K):((Polynomial.C z)^2).coeff 2=0 := by
    rw [←map_pow,Polynomial.coeff_C]; norm_num
  simp [hc]

 

def infinityNumerator {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K) :=
  fun i j:Fin ((n+1)+(n+1)%2) =>
    (augmentedNumerator (Polynomial.C rr) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).coeff
      (scalarEdgeDegree (0:Fin (n+1)) i j)
def infinityDenominator {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K) :=
  fun i j:Fin ((n+1)+(n+1)%2) =>
    (augmentedDenominator (Polynomial.C dd) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).coeff
      (scalarEdgeDegree (0:Fin (n+1)) i j)

lemma augmentedNumerator_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (rr:ℂ) (a:Fin n → K) (i j:Fin ((n+1)+(n+1)%2)) :
      (augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).natDegree ≤
        scalarEdgeDegree (0:Fin (n+1)) i j := by
    have hh: firstScalarHom f a (augmentedNumerator (MvPolynomial.C rr) MvPolynomial.X i j)=
        augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j := by
      simpa only [Matrix.map_apply,firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X'] using
          congrFun (congrFun (map_augmentedNumerator (firstScalarHom f a) (MvPolynomial.C rr) MvPolynomial.X) i) j
    rw [←hh]
    exact (firstScalarHom_degree f a _).trans (augmentedNumerator_degree 0 rr i j)

lemma augmentedDenominator_first_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (dd:ℂ) (a:Fin n → K) (i j:Fin ((n+1)+(n+1)%2)) :
      (augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j).natDegree ≤
        scalarEdgeDegree (0:Fin (n+1)) i j := by
    have hh: firstScalarHom f a (augmentedDenominator (MvPolynomial.C dd) MvPolynomial.X i j)=
        augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))) i j := by
      simpa only [Matrix.map_apply,firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply,
        MvPolynomial.eval₂Hom_X'] using
          congrFun (congrFun (map_augmentedDenominator (firstScalarHom f a) (MvPolynomial.C dd) MvPolynomial.X) i) j
    rw [←hh]
    exact (firstScalarHom_degree f a _).trans (augmentedDenominator_degree 0 dd i j)

lemma firstScalarHom_C {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (z:ℂ) : firstScalarHom f a (MvPolynomial.C z)=Polynomial.C (f z) := by
  simp only [firstScalarHom,MvPolynomial.eval₂Hom_C,RingHom.comp_apply]
lemma firstScalarHom_X {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) (i:Fin (n+1)) : firstScalarHom f a (MvPolynomial.X i)=
      (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)) : Fin (n+1) → Polynomial K) i := by
  simp only [firstScalarHom,MvPolynomial.eval₂Hom_X']

lemma scalarNumerator_first_map {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (a:Fin n → K) :
    firstScalarHom f a (scalarNumerator (n+1) dd rr)=
      clearedPfaffian (Polynomial.C (f ((2^(((n+1)+(n+1)%2)/2)*
        (Nat.factorial (((n+1)+(n+1)%2)/2):ℂ))⁻¹)))
          (augmentedNumerator (Polynomial.C (f rr)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i))))
          (augmentedDenominator (Polynomial.C (f dd)) (Fin.cons Polynomial.X (fun i => Polynomial.C (a i)))) := by
  rw [scalarNumerator,map_clearedPfaffian,map_augmentedNumerator,map_augmentedDenominator]
  simp only [firstScalarHom_C,firstScalarHom_X]

lemma scalarNumerator_first_top {K:Type*} [CommRing K] (f:ℂ →+* K)
    (n:ℕ) (dd rr:ℂ) (a:Fin n → K) :
    (firstScalarHom f a (scalarNumerator (n+1) dd rr)).coeff (2*n)=
      clearedPfaffian (f ((2^(((n+1)+(n+1)%2)/2)*
        (Nat.factorial (((n+1)+(n+1)%2)/2):ℂ))⁻¹))
          (infinityNumerator (f rr) a) (infinityDenominator (f dd) a) := by
  have he:2*n=∑e:UpperPair ((n+1)+(n+1)%2), scalarEdgeDegree (0:Fin (n+1)) e.val.1 e.val.2 := by
    rw [sum_scalarEdgeDegree]; simp
  rw [scalarNumerator_first_map]
  rw [he,clearedPfaffian_top _ _ _ _ (scalarEdgeDegree_symm 0)
      (augmentedNumerator_first_degree f rr a) (augmentedDenominator_first_degree f dd a)]
  rfl


 

 


 
def infinityKernel {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K) :
    Matrix (Fin ((n+1)+(n+1)%2)) (Fin ((n+1)+(n+1)%2)) K := fun i j =>
  if hi:i.val<n+1 then
    if hj:j.val<n+1 then
      if hi0:i.val=0 then
        if j.val=0 then 0 else 1
      else if hj0:j.val=0 then -1
      else plainKernel dd rr a ⟨i.val-1,by omega⟩ ⟨j.val-1,by omega⟩
    else 1
  else if j.val<n+1 then -1 else 0

lemma infinityNumerator_skew {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) :
    infinityNumerator rr a j i= -infinityNumerator rr a i j := by
  rw [infinityNumerator,infinityNumerator,scalarEdgeDegree_symm 0 j i]
  rw [←Polynomial.coeff_neg]
  congr 1
  unfold augmentedNumerator
  split_ifs <;> try ring_nf

lemma infinityDenominator_symm {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) :
    infinityDenominator dd a i j=infinityDenominator dd a j i := by
  rw [infinityDenominator,infinityDenominator,scalarEdgeDegree_symm 0 i j,
    augmentedDenominator_symm]

lemma infinityDenominator_zero_real {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (j:Fin ((n+1)+(n+1)%2)) (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityDenominator dd a 0 j=1 := by
  have he:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityDenominator,augmentedDenominator,Fin.val_zero,Nat.zero_lt_succ,dite_eq_left,
    hj,he,Fin.cons_succ,scalarEdgeDegree,true_or,ite_true,and_self]
  exact polynomial_top_discriminant dd (a ⟨j.val-1,by omega⟩)

lemma infinityNumerator_zero_real {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (j:Fin ((n+1)+(n+1)%2)) (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityNumerator rr a 0 j=1 := by
  have he:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityNumerator,augmentedNumerator,Fin.val_zero,Nat.zero_lt_succ,dite_eq_left,
    hj,he,Fin.cons_succ,scalarEdgeDegree,true_or,ite_true,and_self]
  exact polynomial_top_numerator rr (a ⟨j.val-1,by omega⟩)

lemma infinityDenominator_pos_real {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (hi:i.val<n+1) (hi0:i.val≠0)
    (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityDenominator dd a i j=discriminant dd (a ⟨i.val-1,by omega⟩) (a ⟨j.val-1,by omega⟩) := by
  have hei:(⟨i.val,hi⟩:Fin (n+1))=(⟨i.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  have hej:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityDenominator,augmentedDenominator,hi,hj,dite_eq_left,hei,hej,Fin.cons_succ,
    scalarEdgeDegree,Fin.val_zero,hi0,hj0,or_false,and_false,ite_false]
  have he:discriminant (Polynomial.C dd) (Polynomial.C (a ⟨i.val-1,by omega⟩))
      (Polynomial.C (a ⟨j.val-1,by omega⟩))=Polynomial.C (discriminant dd
        (a ⟨i.val-1,by omega⟩) (a ⟨j.val-1,by omega⟩)) := by
    simp only [discriminant,map_sub,map_add,map_pow,map_mul,map_ofNat]
  rw [he,Polynomial.coeff_C]; rfl

lemma infinityNumerator_pos_real {K:Type*} [CommRing K] {n:ℕ} (rr:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (hi:i.val<n+1) (hi0:i.val≠0)
    (hj:j.val<n+1) (hj0:j.val≠0) :
    infinityNumerator rr a i j=(a ⟨i.val-1,by omega⟩-a ⟨j.val-1,by omega⟩)*
      (a ⟨i.val-1,by omega⟩+a ⟨j.val-1,by omega⟩+rr) := by
  have hei:(⟨i.val,hi⟩:Fin (n+1))=(⟨i.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  have hej:(⟨j.val,hj⟩:Fin (n+1))=(⟨j.val-1,by omega⟩:Fin n).succ := by ext; simp; omega
  simp only [infinityNumerator,augmentedNumerator,hi,hj,dite_eq_left,hei,hej,Fin.cons_succ,
    scalarEdgeDegree,Fin.val_zero,hi0,hj0,or_false,and_false,ite_false]
  rw [←map_add,←map_add,←map_sub,←map_mul,Polynomial.coeff_C]; rfl

lemma infinityDenominator_fake {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K)
    (i j:Fin ((n+1)+(n+1)%2)) (h:¬(i.val<n+1 ∧ j.val<n+1)) :
    infinityDenominator dd a i j=1 := by
  simp only [infinityDenominator,augmentedDenominator,scalarEdgeDegree]
  split_ifs <;> simp_all

lemma infinityKernel_eq {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K) :
    (fun i j => infinityNumerator rr a i j/infinityDenominator dd a i j)=infinityKernel dd rr a := by
  funext i j
  by_cases hi:i.val<n+1
  · by_cases hj:j.val<n+1
    · by_cases hi0:i.val=0
      · have hie:i=0 := Fin.ext hi0
        subst i
        by_cases hj0:j.val=0
        · have hje:j=0 := Fin.ext hj0
          subst j
          simp [infinityNumerator,augmentedNumerator,infinityKernel]
        · rw [infinityNumerator_zero_real rr a j hj hj0,infinityDenominator_zero_real dd a j hj hj0]
          simp [infinityKernel,hj,hj0]
      · by_cases hj0:j.val=0
        · have hje:j=0 := Fin.ext hj0
          subst j
          rw [infinityNumerator_skew,infinityDenominator_symm,
            infinityNumerator_zero_real rr a i hi hi0,infinityDenominator_zero_real dd a i hi hi0]
          simp [infinityKernel,hi,hi0]
        · rw [infinityNumerator_pos_real rr a i j hi hi0 hj hj0,
            infinityDenominator_pos_real dd a i j hi hi0 hj hj0]
          simp [infinityKernel,hi,hj,hi0,hj0,plainKernel]
    · rw [infinityDenominator_fake dd a i j (by tauto)]
      simp [infinityNumerator,augmentedNumerator,scalarEdgeDegree,infinityKernel,hi,hj]
  · rw [infinityDenominator_fake dd a i j (by tauto)]
    by_cases hj:j.val<n+1 <;>
      simp [infinityNumerator,augmentedNumerator,scalarEdgeDegree,infinityKernel,hi,hj]

lemma infinityKernel_real {K:Type*} [Field K] {n:ℕ} (dd rr:K) (a:Fin n → K)
    (i j:Fin (n+1)) :
    infinityKernel dd rr a ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ =
      frontBorder (plainKernel dd rr a) 1 i j := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => simp [infinityKernel]
    | succ j => simp [infinityKernel,show j.val+1<n+1 by omega]
  | succ i =>
    induction j using Fin.cases with
    | zero => simp [infinityKernel,show i.val+1<n+1 by omega]
    | succ j => simp [infinityKernel,show i.val+1<n+1 by omega,
        show j.val+1<n+1 by omega,plainKernel]

lemma pfaffian_infinityKernel {K:Type*} [Field K] [CharZero K] {n:ℕ}
    (dd rr:K) (a:Fin n → K) :
    pfaffian (infinityKernel dd rr a)=pfaffian (augmentedKernel dd rr a) := by
  obtain ⟨m,hm|hm⟩:∃m,n=2*m ∨ n=2*m+1 := ⟨n/2,by omega⟩
  · subst n
    have hs:(2*m+1)+(2*m+1)%2=(2*m+1)+1 := by omega
    apply Eq.trans (pfaffian_cast hs (infinityKernel dd rr a)).symm
    have he:(fun i j => infinityKernel dd rr a (Fin.cast hs.symm i) (Fin.cast hs.symm j))=
        backBorder (frontBorder (plainKernel dd rr a) 1) := by
      funext i j
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp [infinityKernel]
        | cast j => simp [infinityKernel,show j.val<2*m+1 by omega]
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp [infinityKernel,show i.val<2*m+1 by omega]
        | cast j =>
          rw [backBorder_cast_cast]
          exact infinityKernel_real dd rr a i j
    rw [he,pfaffian_back_front _ (plainKernel_skew _ _ _),pfaffian_augmented_even]
  · subst n
    have hs:((2*m+1)+1)+((2*m+1)+1)%2=(2*m+1)+1 := by omega
    apply Eq.trans (pfaffian_cast hs (infinityKernel dd rr a)).symm
    have he:(fun i j => infinityKernel dd rr a (Fin.cast hs.symm i) (Fin.cast hs.symm j))=
        frontBorder (plainKernel dd rr a) 1 := by
      funext i j
      exact infinityKernel_real dd rr a i j
    rw [he,pfaffian_front_back _ (plainKernel_skew _ _ _),pfaffian_augmented_odd]


 

 


def infinityPairEmbed (n:ℕ) (e:UpperPair n) : UpperPair ((n+1)+(n+1)%2) :=
  ⟨(⟨e.val.1.val+1,by omega⟩,⟨e.val.2.val+1,by omega⟩),by simpa using e.property⟩

lemma infinityPairEmbed_injective (n:ℕ) : Function.Injective (infinityPairEmbed n) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext
  · have hh:=congrArg (fun e:UpperPair ((n+1)+(n+1)%2) => e.val.1.val) h
    exact Nat.add_right_cancel hh
  · have hh:=congrArg (fun e:UpperPair ((n+1)+(n+1)%2) => e.val.2.val) h
    exact Nat.add_right_cancel hh

lemma infinityDenominator_product {K:Type*} [CommRing K] {n:ℕ} (dd:K) (a:Fin n → K) :
    (∏e:UpperPair ((n+1)+(n+1)%2),infinityDenominator dd a e.val.1 e.val.2)=
      ∏e:UpperPair n,discriminant dd (a e.val.1) (a e.val.2) := by
  symm
  apply Fintype.prod_of_injective (infinityPairEmbed n) (infinityPairEmbed_injective n)
  · intro e he
    by_cases hi:e.val.1.val<n+1
    · by_cases hj:e.val.2.val<n+1
      · by_cases hi0:e.val.1.val=0
        · have hie:e.val.1=0:=Fin.ext hi0
          rw [hie]
          exact infinityDenominator_zero_real dd a e.val.2 hj (by have := e.property; simp_all; omega)
        · exfalso
          apply he
          refine ⟨⟨(⟨e.val.1.val-1,by omega⟩,⟨e.val.2.val-1,by have:=e.property; omega⟩),?_⟩,?_⟩
          · change e.val.1.val-1<e.val.2.val-1
            have:=e.property; omega
          · apply Subtype.ext; apply Prod.ext <;> apply Fin.ext <;>
              simp only [infinityPairEmbed] <;> have:=e.property <;> omega
      · exact infinityDenominator_fake dd a _ _ (by tauto)
    · exact infinityDenominator_fake dd a _ _ (by tauto)
  · intro e
    rw [infinityDenominator_pos_real dd a _ _ (by dsimp [infinityPairEmbed]; omega)
      (by simp [infinityPairEmbed]) (by dsimp [infinityPairEmbed]; omega) (by simp [infinityPairEmbed])]
    rfl

lemma infinityDenominator_ne {K:Type*} [Field K] {n:ℕ} (dd:K) (a:Fin n → K)
    (hD:∀i j,i≠j → discriminant dd (a i) (a j)≠0)
    (i j:Fin ((n+1)+(n+1)%2)) (hij:i≠j) : infinityDenominator dd a i j≠0 := by
  by_cases hi:i.val<n+1
  · by_cases hj:j.val<n+1
    · by_cases hi0:i.val=0
      · have hie:i=0:=Fin.ext hi0
        subst i
        rw [infinityDenominator_zero_real dd a j hj (by intro h; exact hij (Fin.ext h).symm)]
        exact one_ne_zero
      · by_cases hj0:j.val=0
        · have hje:j=0:=Fin.ext hj0
          subst j
          rw [infinityDenominator_symm,infinityDenominator_zero_real dd a i hi hi0]
          exact one_ne_zero
        · rw [infinityDenominator_pos_real dd a i j hi hi0 hj hj0]
          apply hD
          intro h
          have hh:=congrArg Fin.val h
          dsimp at hh
          apply hij
          apply Fin.ext
          omega
    · rw [infinityDenominator_fake dd a _ _ (by tauto)]; exact one_ne_zero
  · rw [infinityDenominator_fake dd a _ _ (by tauto)]; exact one_ne_zero

lemma scalarNumerator_first_top_eval {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (a:Fin n → K)
    (hD:∀i j,i≠j → discriminant (f dd) (a i) (a j)≠0) :
    (firstScalarHom f a (scalarNumerator (n+1) dd rr)).coeff (2*n)=
      MvPolynomial.eval₂Hom f a (scalarNumerator n dd rr) := by
  rw [scalarNumerator_first_top]
  simp only [map_inv₀,map_mul,map_pow,map_ofNat,map_natCast]
  refine (clear_pfaffian (infinityNumerator (f rr) a) (infinityDenominator (f dd) a)
    (infinityDenominator_symm _ _) (infinityDenominator_ne _ _ hD)).symm.trans ?_
  rw [infinityKernel_eq,pfaffian_infinityKernel,infinityDenominator_product,
    scalarNumerator_eval f n dd rr a hD,product_augmentedDenominator,←prod_upperPair]

lemma firstScalarHom_vandermonde {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))=
      (∏i:Fin n,(Polynomial.X-Polynomial.C (a i)))*Polynomial.C (sourceVandermonde a) := by
  rw [map_sourceVandermonde]
  simp only [firstScalarHom_X,sourceVandermonde]
  let v:Fin (n+1) → Polynomial K := Fin.cons Polynomial.X (fun i =>Polynomial.C (a i))
  have h:=prod_upperPair_succ (fun i j:Fin (n+1) => v i-v j)
  apply Eq.trans h
  simp only [v,Fin.cons_zero,Fin.cons_succ,map_prod,map_sub]

lemma firstScalarHom_vandermonde_degree {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    (firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))).natDegree ≤ n := by
  rw [firstScalarHom_vandermonde]
  apply (Polynomial.natDegree_mul_C_le _ _).trans
  exact (Polynomial.natDegree_prod_le _ _).trans ((Finset.sum_le_sum
    (fun i _ => Polynomial.natDegree_X_sub_C_le (a i))).trans (by simp))

lemma firstScalarHom_vandermonde_top {K:Type*} [CommRing K] (f:ℂ →+* K)
    {n:ℕ} (a:Fin n → K) :
    (firstScalarHom f a (sourceVandermonde (MvPolynomial.X:Fin (n+1) → CosineRing (n+1)))).coeff n=
      sourceVandermonde a := by
  rw [firstScalarHom_vandermonde,Polynomial.coeff_mul_C]
  have he:n=∑i:Fin n,(1:ℕ) := by simp
  have hh:=coeff_prod_budget Finset.univ (fun i:Fin n => (Polynomial.X-Polynomial.C (a i)))
    (fun _ => 1) (by intro i _; exact Polynomial.natDegree_X_sub_C_le _)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one,
    Polynomial.coeff_sub,Polynomial.coeff_X_one,Polynomial.coeff_C] at hh
  rw [hh]; simp

 

theorem scalarPolynomial_first_top {K:Type*} [Field K] [CharZero K]
    (f:ℂ →+* K) (n:ℕ) (dd rr:ℂ) (hdd:dd≠0) (a:Fin n → K)
    (ha:Function.Injective a) (hD:∀i j,i≠j → discriminant (f dd) (a i) (a j)≠0) :
    (firstScalarHom f a (scalarPolynomial (n+1) dd rr hdd)).coeff n=
      MvPolynomial.eval₂Hom f a (scalarPolynomial n dd rr hdd) := by
  have hh:=scalarNumerator_first_top_eval f n dd rr a hD
  rw [scalarNumerator_eq_vandermonde (n+1) dd rr hdd,map_mul (firstScalarHom f a),
    show 2*n=n+n by omega,
    Polynomial.coeff_mul_add_eq_of_natDegree_le (firstScalarHom_vandermonde_degree f a)
      (scalarPolynomial_first_degree f n dd rr hdd a),firstScalarHom_vandermonde_top,
    scalarNumerator_eq_vandermonde n dd rr hdd,map_mul (MvPolynomial.eval₂Hom f a),
    map_sourceVandermonde] at hh
  simp only [MvPolynomial.eval₂Hom_X'] at hh
  exact mul_left_cancel₀ (sourceVandermonde_ne_zero a ha) hh

end
end CriticalStrip.Diagram

end OAI
