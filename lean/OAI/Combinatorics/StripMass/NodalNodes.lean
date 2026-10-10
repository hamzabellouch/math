import Mathlib
import OAI.Combinatorics.StripMass.AugmentedTail

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/



namespace CriticalStrip.Diagram
noncomputable section

 
def cosineL {n : ℕ} (e : Fin n → ℤ) (z : ℂ) : Laurent n :=
  monomialL e (z/2) + monomialL (-e) (z⁻¹/2)

theorem cosineL_map {n : ℕ} (e : Fin n → ℤ) (z : ℂ) (hz : z ≠ 0) :
    evalLaurent (cosineL e z) = torusCos (evalLaurent (monomialL e z)) := by
  rw [cosineL, evalLaurent, map_add, torusCos, evalLaurent, map_monomialL_inv e z hz]
  rw [map_monomialL_factor e (z/2), map_monomialL_factor (-e) (z⁻¹/2),
    map_monomialL_factor e z, map_monomialL_factor (-e) z⁻¹]
  simp only [constF, map_div₀, map_ofNat]
  ring

theorem twice_variableExponent_ne_neg {n : ℕ} (i j : Fin n) :
    (2 : ℤ) • variableExponent i ≠ -((2 : ℤ) • variableExponent j) := by
  intro h
  have hi := congrFun h i
  by_cases hij : i = j
  · subst j
    simp [variableExponent] at hi
  · simp [variableExponent, eq_comm, hij] at hi

theorem twice_variableExponent_injective {n : ℕ} :
    Function.Injective (fun i : Fin n => (2 : ℤ) • variableExponent i) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  simp [variableExponent, eq_comm, hij] at hi

theorem cosineL_two_injective {n : ℕ} (z : ℂ) (hz : z ≠ 0) :
    Function.Injective (fun i : Fin n => cosineL ((2 : ℤ) • variableExponent i) z) := by
  intro i j h
  by_contra hij
  have he : (2 : ℤ) • variableExponent i ≠ (2 : ℤ) • variableExponent j :=
    fun h => hij (twice_variableExponent_injective h)
  have hh := congrArg (fun f : Laurent n => f.coeff ((2 : ℤ) • variableExponent i)) h
  simp only [cosineL, monomialL, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply, Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm, ite_eq_right (twice_variableExponent_ne_neg i j).symm,
    add_zero] at hh
  exact hz ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

theorem map_monomialL_two_variable {n : ℕ} (i : Fin n) (z : ℂ) :
    evalLaurent (monomialL ((2 : ℤ) • variableExponent i) z) =
      constF n z * variableF i ^ 2 := by
  have hh : monomialL ((2 : ℤ) • variableExponent i) (1:ℂ) =
      monomialL (variableExponent i) 1 ^ 2 := by
    simp [pow_two, two_smul]
  rw [evalLaurent, map_monomialL_factor, hh, map_pow]
  rfl

theorem deletionBeta_laurent {n : ℕ} (i : Fin n) :
    deletionBeta i = evalLaurent (cosineL ((2 : ℤ) • variableExponent i) (phase^3)) := by
  rw [cosineL_map _ _ (pow_ne_zero _ phase_ne_zero), map_monomialL_two_variable]
  unfold deletionBeta deletionNode
  congr 1
  simp only [constF, map_pow]
  field_simp [constF_phase_ne_zero]

theorem deletionBeta_injective (n : ℕ) : Function.Injective (@deletionBeta n) := by
  intro i j h
  rw [deletionBeta_laurent, deletionBeta_laurent] at h
  exact cosineL_two_injective _ (pow_ne_zero _ phase_ne_zero)
    (IsFractionRing.injective (SpectralRing n) (SpectralField n) h)

theorem deletionNode_sine_ne_zero {n : ℕ} (i : Fin n) : torusSin (deletionNode i) ≠ 0 := by
  have hs : evalLaurent (sineL (variableExponent i) (phase^3)) = torusSin (deletionNode i) := by
    rw [evalLaurent, map_sine_variable_nat]
    congr 1
    exact mul_comm ..
  rw [← hs]
  apply (IsFractionRing.to_map_eq_zero_iff.not).2
  intro he
  have hz := congrArg (flatEval n) he
  have hflat : flatEval n (sineL (variableExponent i) (phase^3)) =
      (Real.sin (3*lambda) : ℂ) := by
    simpa only [zpow_ofNat, Int.cast_ofNat] using flatEval_sine_phase (variableExponent i) 3
  rw [hflat, map_zero] at hz
  have hd := flatEval_rowDenominator_ne_zero i
  rw [flatEval_rowDenominator, hz, zero_mul] at hd
  exact hd rfl


 

 

open scoped LaurentPolynomial Classical

def variableUnit {n : ℕ} (i : Fin n) : (Laurent n)ˣ := monomialUnit (variableExponent i) 1 one_ne_zero

def constantUnit (n : ℕ) (z : ℂ) (hz:z≠0) : (Laurent n)ˣ := monomialUnit 0 z hz

def betaL {n : ℕ} (i : Fin n) : Laurent n := cosineL ((2:ℤ) • variableExponent i) (phase^3)

@[simp] lemma betaL_map {n : ℕ} (i : Fin n) : evalLaurent (betaL i)=deletionBeta i :=
  (deletionBeta_laurent i).symm

lemma variableExponent_ne_neg {n : ℕ} (i : Fin n) : variableExponent i≠-variableExponent i := by
  intro h
  have hh:=congrFun h i
  simp [variableExponent] at hh

lemma collisionRoots_injective {n : ℕ} (j : Fin n) :
    Function.Injective (cosineCollisionRoots (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j)) := by
  intro k l h
  have hp:=congrArg (fun v : (Laurent n)ˣ => (v:Laurent n).coeff (variableExponent j)) h
  have hn:=congrArg (fun v : (Laurent n)ˣ => (v:Laurent n).coeff (-variableExponent j)) h
  fin_cases k <;> fin_cases l <;> try rfl
  all_goals dsimp [cosineCollisionRoots,constantUnit,variableUnit,monomialUnit] at hp hn
  all_goals try simp only [monomialL_mul,zero_add,mul_one,neg_zero,inv_one] at hp hn
  all_goals simp [monomialL,variableExponent_ne_neg j,(variableExponent_ne_neg j).symm] at hp hn
  all_goals try norm_num at hp
  all_goals exfalso; apply inv_ne_zero (pow_ne_zero 3 phase_ne_zero)
  all_goals first | linear_combination hn / 2 | linear_combination -hn / 2

lemma peel_betaL_self {n : ℕ} (i : Fin (n+1)) :
    peelLaurentEquiv i (betaL i)=
      LaurentPolynomial.C (constantL n (phase^3/2))*LaurentPolynomial.T 2+
      LaurentPolynomial.C (constantL n ((phase^3)⁻¹/2))*LaurentPolynomial.T (-2) := by
  have hrem:Fin.removeNth i ((2:ℤ) • variableExponent i)=0 := by
    funext j
    simp [Fin.removeNth,variableExponent,Fin.succAbove_ne]
  have hval:((2:ℤ) • variableExponent i) i=2 := by simp [variableExponent]
  simp only [betaL,cosineL,map_add,peelLaurentEquiv_monomial,hval,hrem,Pi.neg_apply]
  have hn:Fin.removeNth i (-((2:ℤ) • variableExponent i))=0 := by
    funext j
    change -(Fin.removeNth i ((2:ℤ) • variableExponent i) j)=0
    rw [hrem]; rfl
  rw [hn]
  simp only [LaurentPolynomial.single_eq_C_mul_T]
  rfl

lemma insert_betaL {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    insertLaurent i (betaL j)=betaL (i.succAbove j) := by
  simp only [betaL,cosineL,map_add,insertLaurent_monomial]
  congr 2
  all_goals funext k; refine Fin.succAboveCases i ?_ (fun l => ?_) k
  all_goals simp [variableExponent,Pi.single_apply,eq_comm]

lemma peel_betaL_other {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    peelLaurentEquiv i (betaL (i.succAbove j))=LaurentPolynomial.C (betaL j) := by
  rw [←insert_betaL i j,peelLaurentEquiv_insert]

@[simp] lemma variableUnit_coe {n : ℕ} (j : Fin n) :
    (variableUnit j : Laurent n)=monomialL (variableExponent j) 1 := rfl
@[simp] lemma variableUnit_inv_coe {n : ℕ} (j : Fin n) :
    ((variableUnit j)⁻¹ : (Laurent n)ˣ).val=monomialL (-variableExponent j) 1 := by
  simp only [variableUnit,monomialUnit,Units.inv_mk,Units.val_mk,inv_one]
@[simp] lemma constantUnit_coe (n : ℕ) (z : ℂ) (hz:z≠0) :
    (constantUnit n z hz : Laurent n)=monomialL 0 z := rfl
@[simp] lemma constantUnit_inv_coe (n : ℕ) (z : ℂ) (hz:z≠0) :
    ((constantUnit n z hz)⁻¹ : (Laurent n)ˣ).val=monomialL 0 z⁻¹ := by
  simp only [constantUnit,monomialUnit,Units.inv_mk,Units.val_mk,neg_zero]

lemma betaL_monomial_expression {n : ℕ} (j : Fin n) :
    monomialL 0 2*(cosineL ((2:ℤ) • variableExponent j) (phase^3))=
    monomialL 0 (phase^3)*(monomialL (variableExponent j) 1)^2+
    monomialL 0 ((phase^3)⁻¹)*(monomialL (-variableExponent j) 1)^2 := by
  simp only [cosineL,pow_two,mul_add,monomialL_mul,zero_add,mul_one,two_smul,neg_add]
  congr 2 <;> ring

lemma betaL_unit_expression {n : ℕ} (j : Fin n) :
    (constantL n 2)*betaL j=
      (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero) : Laurent n)*(variableUnit j : Laurent n)^2+
      (((constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))⁻¹ : (Laurent n)ˣ) : Laurent n)*
        (((variableUnit j)⁻¹ : (Laurent n)ˣ) : Laurent n)^2 := by
  simp only [variableUnit_coe,variableUnit_inv_coe,constantUnit_coe,constantUnit_inv_coe]
  exact betaL_monomial_expression j

lemma cosineCollisionPacket_betaL {n : ℕ} (i : Fin (n+1)) (j : Fin n) :
    cosineCollisionPacket (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j)=
      2*(peelLaurentEquiv i (betaL i-betaL (i.succAbove j))) := by
  rw [map_sub,peel_betaL_self,peel_betaL_other,cosineCollisionPacket,←betaL_unit_expression]
  simp only [map_mul,constantUnit,monomialUnit]
  have h1 : (2:LaurentPolynomial (Laurent n))*LaurentPolynomial.C (constantL n (phase^3/2))=
      LaurentPolynomial.C (constantL n (phase^3)) := by
    rw [←map_ofNat LaurentPolynomial.C 2,←map_mul,←map_ofNat (constantL n) 2,←map_mul]
    congr 2
    ring
  have h2 : (2:LaurentPolynomial (Laurent n))*LaurentPolynomial.C (constantL n ((phase^3)⁻¹/2))=
      LaurentPolynomial.C (constantL n ((phase^3)⁻¹)) := by
    rw [←map_ofNat LaurentPolynomial.C 2,←map_mul,←map_ofNat (constantL n) 2,←map_mul]
    congr 2
    ring
  change LaurentPolynomial.C (constantL n (phase^3))*LaurentPolynomial.T 2+
    LaurentPolynomial.C (constantL n ((phase^3)⁻¹))*LaurentPolynomial.T (-2)-
    LaurentPolynomial.C (constantL n 2)*LaurentPolynomial.C (betaL j)=_
  simp only [map_ofNat]
  linear_combination -(LaurentPolynomial.T 2)*h1-(LaurentPolynomial.T (-2))*h2

 
lemma betaL_difference_dvd {n : ℕ} (i : Fin (n+1)) (j : Fin n) (f : Laurent (n+1))
    (h:∀ k, substituteLaurent i
      (cosineCollisionRoots (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero)) (variableUnit j) k) f=0) :
    betaL i-betaL (i.succAbove j) ∣ f := by
  have hh:=cosineCollisionPacket_dvd (constantUnit n (phase^3) (pow_ne_zero _ phase_ne_zero))
    (variableUnit j) (collisionRoots_injective j) (peelLaurentEquiv i f) h
  rw [cosineCollisionPacket_betaL i j] at hh
  have hdiv : peelLaurentEquiv i (betaL i-betaL (i.succAbove j)) ∣ peelLaurentEquiv i f :=
    dvd_trans (dvd_mul_left _ _) hh
  exact (map_dvd_iff (peelLaurentEquiv i)).mp hdiv

end

 

 

noncomputable section
open scoped Classical LaurentPolynomial

lemma sum_upperPair {R:Type*} [AddCommMonoid R] {n:ℕ} (D:Fin n → Fin n → R) :
    (∑ e:UpperPair n,D e.val.1 e.val.2)=∑ i,∑ j∈Finset.Ioi i,D i j := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun ij:Fin n × Fin n => ij.1 < ij.2))
    (by simp) (fun ij:Fin n × Fin n => D ij.1 ij.2),Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have h:Finset.Ioi i=Finset.univ.filter (fun j => i<j) := by ext j; simp
  rw [h,Finset.sum_filter]

lemma upperPair_incidence_sum {n:ℕ} (k:Fin (n+1)) :
    (∑ e:UpperPair (n+1), ((if e.val.1=k then 1 else 0)+(if e.val.2=k then 1 else 0):ℕ))=n := by
  rw [sum_upperPair (fun i j => ((if i=k then 1 else 0)+(if j=k then 1 else 0):ℕ))]
  simp_rw [Finset.sum_add_distrib]
  have h1:(∑ i:Fin (n+1),∑ _j∈Finset.Ioi i,(if i=k then 1 else 0:ℕ))=n-k.val := by
    simp only [Finset.sum_const,smul_eq_mul]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Fin.card_Ioi]
    omega
  have h2:(∑ i:Fin (n+1),∑ j∈Finset.Ioi i,(if j=k then 1 else 0:ℕ))=k.val := by
    simp only [Finset.sum_ite_eq',Finset.mem_Ioi]
    rw [←Finset.sum_filter]
    have h:Finset.univ.filter (fun i:Fin (n+1) => i<k)=Finset.Iio k := by ext i; simp
    rw [h]
    simp only [Finset.sum_const,smul_eq_mul,mul_one,Fin.card_Iio]
  rw [h1,h2]
  have :=k.isLt
  omega

lemma LaurentInterval.mul {K:Type*} [Field K] {f g:LaurentPolynomial K} {a b c d:ℤ}
    (hf:LaurentInterval f a b) (hg:LaurentInterval g c d) : LaurentInterval (f*g) (a+c) (b+d) := by
  intro e he
  have hs:=AddMonoidAlgebra.support_coeff_mul_subset f g (Finsupp.mem_support_iff.mpr he)
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.mem_add.mp hs
  have hx:=hf x (Finsupp.mem_support_iff.mp hx)
  have hy:=hg y (Finsupp.mem_support_iff.mp hy)
  omega

lemma LaurentInterval.prod_exact {K:Type*} [Field K] {ι:Type*} (s:Finset ι)
    (f:ι → LaurentPolynomial K) (a b:ι → ℤ)
    (h:∀ i∈s,LaurentInterval (f i) (a i) (b i) ∧ (f i).coeff (a i)≠0 ∧ (f i).coeff (b i)≠0) :
    LaurentInterval (∏ i∈s,f i) (∑ i∈s,a i) (∑ i∈s,b i) ∧
      (∏ i∈s,f i).coeff (∑ i∈s,a i)≠0 ∧ (∏ i∈s,f i).coeff (∑ i∈s,b i)≠0 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    refine ⟨?_,?_,?_⟩
    · intro e he
      have : e=0 := by
        by_contra hh
        apply he
        change (Finsupp.single (0:ℤ) (1:K)) e=0
        exact Finsupp.single_eq_of_ne hh
      simp [this]
    · simp
    · simp
  | @insert i s hi ih =>
    specialize ih (fun j hj => h j (by simp [hj]))
    have hj:=h i (by simp)
    rw [Finset.prod_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]
    refine ⟨hj.1.mul ih.1,?_,?_⟩
    · rw [laurent_mul_bottom_coeff _ _ _ _ (fun e he => (hj.1 e he).1) (fun e he => (ih.1 e he).1)]
      exact mul_ne_zero hj.2.1 ih.2.1
    · rw [laurent_mul_top_coeff _ _ _ _ (fun e he => (hj.1 e he).2) (fun e he => (ih.1 e he).2)]
      exact mul_ne_zero hj.2.2 ih.2.2

lemma peel_beta_coeff_self {n:ℕ} (i:Fin (n+1)) (e:ℤ) :
    (peelLaurent i (betaL i)).coeff e=
      (if e=2 then constF n (phase^3/2) else 0)+(if e=(-2) then constF n ((phase^3)⁻¹/2) else 0) := by
  rw [peelLaurent_coeff,peel_betaL_self]
  simp only [←LaurentPolynomial.single_eq_C_mul_T,AddMonoidAlgebra.coeff_add,
    AddMonoidAlgebra.coeff_single,Finsupp.add_apply]
  change (algebraMap (SpectralRing n) (SpectralField n))
    ((Finsupp.single 2 (constantL n (phase^3/2))) e +
      (Finsupp.single (-2) (constantL n ((phase^3)⁻¹/2))) e)=_
  simp only [Finsupp.single_apply]
  rw [map_add]
  congr 1
  · by_cases h:e=2
    · subst e
      rw [ite_eq_left rfl,ite_eq_left rfl]
      exact map_constantL n _
    · rw [ite_eq_right (Ne.symm h),ite_eq_right h,map_zero]
  · by_cases h:e=(-2)
    · subst e
      rw [ite_eq_left rfl,ite_eq_left rfl]
      exact map_constantL n _
    · rw [ite_eq_right (Ne.symm h),ite_eq_right h,map_zero]

lemma peel_beta_coeff_other {n:ℕ} (i:Fin (n+1)) (j:Fin n) (e:ℤ) :
    (peelLaurent i (betaL (i.succAbove j))).coeff e=if e=0 then deletionBeta j else 0 := by
  rw [peelLaurent_coeff,peel_betaL_other]
  change evalLaurent ((AddMonoidAlgebra.single 0 (betaL j)).coeff e)=_
  simp only [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
  by_cases h:e=0
  · subst e
    rw [ite_eq_left rfl,ite_eq_left rfl]
    exact betaL_map j
  · rw [ite_eq_right (Ne.symm h),ite_eq_right h]
    exact map_zero _

end

 

 

noncomputable section

instance spectralFieldCharZero (n : ℕ) : CharZero (SpectralField n) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (SpectralField n)).injective


 

 


lemma torusCos_sum {n : ℕ} (z w : SpectralField n) (hz : z≠0) (hw : w≠0) :
    torusCos (z/w)+torusCos (z*w)=2*torusCos z*torusCos w := by
  unfold torusCos
  field_simp [hz,hw]
  ring

lemma torusCos_product {n : ℕ} (z w : SpectralField n) (hz : z≠0) (hw : w≠0) :
    torusCos (z/w)*torusCos (z*w)=(torusCos z)^2+(torusCos w)^2-1 := by
  unfold torusCos
  field_simp [hz,hw]
  norm_num
  ring

lemma discriminant_torus_roots {n : ℕ} (z t : SpectralField n) (hz : z≠0) :
    discriminant (constF n d) (torusCos z) t=
      (t-torusCos (z/constF n phase^6))*(t-torusCos (z*constF n phase^6)) := by
  have hq := pow_ne_zero 6 (constF_phase_ne_zero n)
  have h6 : torusCos (constF n phase^6) = -constF n d := by
    rw [torusCos_phase_pow]
    simp only [Nat.cast_ofNat,cos_six_lambda,Complex.ofReal_neg,constF,map_neg]
  have hd : (constF n d)^2=1/2 := by
    have h:=congrArg (fun a : ℝ => constF n (a:ℂ)) d_sq
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,
      constF,map_pow,map_div₀,map_one,map_ofNat] using h
  have hs:=torusCos_sum z (constF n phase^6) hz hq
  have hp:=torusCos_product z (constF n phase^6) hz hq
  rw [h6] at hs hp
  unfold discriminant
  linear_combination t*hs-hp-2*hd

lemma cosineL_two_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (z w : ℂ) (hz : z≠0) :
    cosineL ((2:ℤ) • variableExponent i) z≠cosineL ((2:ℤ) • variableExponent j) w := by
  intro h
  have he : (2 : ℤ) • variableExponent i ≠ (2 : ℤ) • variableExponent j :=
    fun h => hij (twice_variableExponent_injective h)
  have hh:=congrArg (fun f : Laurent n => f.coeff ((2:ℤ) • variableExponent i)) h
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,
    ite_eq_right he.symm,ite_eq_right (twice_variableExponent_ne_neg i j).symm,add_zero] at hh
  exact hz ((div_eq_zero_iff).mp hh |>.resolve_right (by norm_num))

lemma cosineL_two_parameter {n : ℕ} (i : Fin n) (z w : ℂ) :
    cosineL ((2:ℤ) • variableExponent i) z=cosineL ((2:ℤ) • variableExponent i) w → z=w := by
  intro h
  have hh:=congrArg (fun f : Laurent n => f.coeff ((2:ℤ) • variableExponent i)) h
  simp only [cosineL,monomialL,AddMonoidAlgebra.coeff_add,AddMonoidAlgebra.coeff_single,
    Finsupp.add_apply,Finsupp.single_apply] at hh
  simp only [ite_eq_right (twice_variableExponent_ne_neg i i).symm,add_zero] at hh
  exact (div_left_inj' (by norm_num : (2:ℂ)≠0)).mp hh

 
def shiftedCosine {n : ℕ} (i : Fin n) (z : ℂ) : SpectralField n :=
  evalLaurent (cosineL ((2:ℤ) • variableExponent i) z)

lemma shiftedCosine_eq {n : ℕ} (i : Fin n) (z : ℂ) (hz : z≠0) :
    shiftedCosine i z=torusCos (constF n z*variableF i^2) := by
  rw [shiftedCosine,cosineL_map _ _ hz,map_monomialL_two_variable]

lemma shiftedCosine_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (z w : ℂ) (hz : z≠0) :
    shiftedCosine i z≠shiftedCosine j w := by
  intro h
  exact cosineL_two_ne i j hij z w hz ((IsFractionRing.injective (SpectralRing n) (SpectralField n)) h)

lemma shiftedCosine_parameter {n : ℕ} (i : Fin n) (z w : ℂ) :
    shiftedCosine i z=shiftedCosine i w → z=w := by
  intro h
  exact cosineL_two_parameter i z w ((IsFractionRing.injective (SpectralRing n) (SpectralField n)) h)

lemma spectralA_shiftedCosine {n : ℕ} (i : Fin n) : spectralA i=shiftedCosine i (phase^(-3:ℤ)) := by
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero)]
  simp only [spectralA,constF,zpow_neg,zpow_ofNat,map_inv₀,map_pow,div_eq_mul_inv,mul_comm]

lemma deletionBeta_shiftedCosine {n : ℕ} (i : Fin n) :
    deletionBeta i=shiftedCosine i (phase^(3:ℤ)) := deletionBeta_laurent i


 

 


lemma shiftedCosine_roots {n : ℕ} (i : Fin n) (k : ℤ) (t : SpectralField n) :
    discriminant (constF n d) (shiftedCosine i (phase^k)) t=
      (t-shiftedCosine i (phase^(k-6)))*(t-shiftedCosine i (phase^(k+6))) := by
  rw [shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    shiftedCosine_eq _ _ (zpow_ne_zero _ phase_ne_zero),
    discriminant_torus_roots _ _ (mul_ne_zero (by
      simpa only [constF,map_zero] using (algebraMap ℂ (SpectralField n)).injective.ne (zpow_ne_zero k phase_ne_zero)) (pow_ne_zero _ (variableF_ne_zero i)))]
  have hq := constF_phase_ne_zero n
  simp only [constF,map_zpow₀,zpow_sub₀ phase_ne_zero,zpow_add₀ phase_ne_zero,
    map_div₀,map_mul,map_pow,zpow_ofNat]
  congr 2 <;> congr 1 <;> ring

lemma shiftedCosine_discriminant_ne {n : ℕ} (i j : Fin n) (hij : i≠j) (k l : ℤ) :
    discriminant (constF n d) (shiftedCosine i (phase^k)) (shiftedCosine j (phase^l))≠0 := by
  rw [shiftedCosine_roots]
  exact mul_ne_zero (sub_ne_zero.mpr (shiftedCosine_ne j i hij.symm _ _ (zpow_ne_zero _ phase_ne_zero)))
    (sub_ne_zero.mpr (shiftedCosine_ne j i hij.symm _ _ (zpow_ne_zero _ phase_ne_zero)))

lemma phase_six_ne_one : phase^(6:ℕ)≠1 := by
  intro h
  have h₃ : phase^(24:ℕ)=1 := by simpa only [←pow_mul,one_pow] using congrArg (fun z : ℂ => z^(4:ℕ)) h
  have h₂ : phase^24=-1 := by
    calc
      _ = (phase^8)^3 := by rw [←pow_mul]
      _ = -1 := by rw [phase_eight]; norm_num
  rw [h₃] at h₂
  norm_num at h₂

lemma spectralA_ne_deletionBeta {n : ℕ} (i : Fin n) : spectralA i≠deletionBeta i := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine]
  intro hh
  have h:=shiftedCosine_parameter i _ _ hh
  simp only [zpow_neg,zpow_ofNat] at h
  have hp : phase^6=1 := by
    calc
      _ = phase^3*phase^3 := by ring
      _ = (phase^3)⁻¹*phase^3 := by rw [h]
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ phase_ne_zero)
  exact phase_six_ne_one hp

lemma spectralA_roots {n : ℕ} (i : Fin n) (t : SpectralField n) :
    discriminant (constF n d) (spectralA i) t=
      (t-deletionBeta i)*(t-shiftedCosine i (phase^(-9:ℤ))) := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine,shiftedCosine_roots]
  norm_num
  ring

lemma deletionBeta_roots {n : ℕ} (i : Fin n) (t : SpectralField n) :
    discriminant (constF n d) (deletionBeta i) t=
      (t-spectralA i)*(t-shiftedCosine i (phase^(9:ℤ))) := by
  rw [spectralA_shiftedCosine,deletionBeta_shiftedCosine,shiftedCosine_roots]
  norm_num

end
end CriticalStrip.Diagram

end OAI
