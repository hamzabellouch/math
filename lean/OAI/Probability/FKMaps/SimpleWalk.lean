import OAI.Probability.FKMaps.HeightTightness

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk

/-- Exact probabilities for the symmetric nearest-neighbour walk on the integers. -/
def kernel : ℕ → ℤ → ℝ
  | 0,z => if z=0 then 1 else 0
  | n+1,z => (kernel n (z-1)+kernel n (z+1))/2

@[simp] lemma kernel_zero (z : ℤ) : kernel 0 z = if z=0 then 1 else 0 := rfl
lemma kernel_succ (n : ℕ) (z : ℤ) : kernel (n+1) z = (kernel n (z-1)+kernel n (z+1))/2 := rfl
lemma kernel_symm (n : ℕ) (z : ℤ) : kernel n (-z)=kernel n z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [kernel_succ,kernel_succ,show -z-1=-(z+1) by ring,show -z+1=-(z-1) by ring,ih,ih]
    ring
lemma kernel_nonneg (n : ℕ) (z : ℤ) : 0≤kernel n z := by
  induction n generalizing z with
  | zero => rw [kernel_zero]; split_ifs <;> norm_num
  | succ n ih => exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)
lemma kernel_support (n : ℕ) (z : ℤ) (h : (n:ℤ) < |z|) : kernel n z=0 := by
  induction n generalizing z with
  | zero =>
    have hz : z≠0 := by intro hz; subst z; norm_num at h
    simp [hz]
  | succ n ih =>
    have ha := abs_sub_abs_le_abs_sub z (1:ℤ)
    norm_num at ha
    have h1 : (n:ℤ) < |z-1| := by omega
    have hb := abs_sub_abs_le_abs_sub z (-1:ℤ)
    norm_num at hb
    have h2 : (n:ℤ) < |z+1| := by omega
    rw [kernel_succ,ih _ h1,ih _ h2]; norm_num

/-- The walk killed on first visiting -1, with both endpoints nonnegative. -/
def killed : ℕ → ℕ → ℕ → ℝ
  | 0,a,b => if a=b then 1 else 0
  | n+1,0,b => killed n 1 b/2
  | n+1,a+1,b => (killed n a b+killed n (a+2) b)/2

lemma killed_nonneg (n a b : ℕ) : 0≤killed n a b := by
  induction n generalizing a with
  | zero => simp only [killed]; split_ifs <;> norm_num
  | succ n ih => cases a with
    | zero => exact div_nonneg (ih _) (by norm_num)
    | succ a => exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)

/-- Discrete reflection principle; this is an identity of the actual killed
transition recursion, not an assumed excursion law. -/
theorem killed_reflection (n a b : ℕ) :
    killed n a b = kernel n ((b:ℤ)-a)-kernel n ((b:ℤ)+a+2) := by
  induction n generalizing a with
  | zero =>
    simp only [killed,kernel_zero]
    have hp : (b:ℤ)+a+2≠0 := by omega
    have he : (b:ℤ)-a=0 ↔ a=b := by omega
    simp only [hp,he,ite_false,sub_zero]
  | succ n ih =>
    cases a with
    | zero =>
      simp only [killed,ih,Nat.cast_zero,sub_zero,add_zero,Nat.cast_one]
      rw [kernel_succ,kernel_succ]
      simp only [show (b:ℤ)+2-1=b+1 by ring,show (b:ℤ)+2+1=b+1+2 by ring]
      ring
    | succ a =>
      simp only [killed,ih,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      rw [kernel_succ,kernel_succ]
      have h1 : (b:ℤ)-(a+1)-1=b-(a+2) := by ring
      have h2 : (b:ℤ)-(a+1)+1=b-a := by ring
      have h3 : (b:ℤ)+(a+1)+2-1=b+a+2 := by ring
      have h4 : (b:ℤ)+(a+1)+2+1=b+(a+2)+2 := by ring
      rw [h1,h2,h3,h4]
      ring

lemma killed_symm (n a b : ℕ) : killed n a b=killed n b a := by
  rw [killed_reflection,killed_reflection,show (a:ℤ)-b=-((b:ℤ)-a) by ring,kernel_symm]
  congr 2; ring

/-- Binomial coefficients extended by zero to negative lower arguments. -/
def chooseInt (n : ℕ) (k : ℤ) : ℝ := if 0≤k then (n.choose k.toNat:ℝ) else 0

lemma chooseInt_zero (k : ℤ) : chooseInt 0 k = if k=0 then 1 else 0 := by
  by_cases hk : 0≤k
  · have he : k.toNat=0 ↔ k=0 := by omega
    rw [chooseInt,ite_eq_left hk]
    by_cases hz : k=0
    · simp [hz]
    · rw [ite_eq_right hz,Nat.choose_eq_zero_of_lt (by omega : 0<k.toNat)]; simp
  · have hn : k≠0 := by omega
    simp [chooseInt,hk,hn]

lemma chooseInt_pascal (n : ℕ) (k : ℤ) :
    chooseInt (n+1) k=chooseInt n (k-1)+chooseInt n k := by
  by_cases hk : 0<k
  · have hk0 : 0≤k := by omega
    have hk1 : 0≤k-1 := by omega
    have he : k.toNat=(k-1).toNat+1 := by omega
    simp only [chooseInt,hk0,hk1,ite_true]
    rw [he,Nat.choose_succ_succ,Nat.cast_add]
  · by_cases hz : k=0
    · subst k; simp [chooseInt]
    · have hneg : ¬0≤k := by omega
      have hneg' : ¬0≤k-1 := by omega
      simp only [chooseInt,hneg,hneg',ite_false,add_zero]

lemma kernel_binomial (n : ℕ) (z : ℤ) :
    kernel n z = if (z+n)%2=0 then chooseInt n ((z+n)/2)/(2:ℝ)^n else 0 := by
  induction n generalizing z with
  | zero =>
    rw [kernel_zero,chooseInt_zero]
    by_cases h : z=0
    · simp [h]
    · have hz : (z+0)%2=0 → (z+0)/2≠0 := by omega
      split_ifs <;> simp_all
  | succ n ih =>
    rw [kernel_succ,ih,ih]
    have hcast : (↑(n+1):ℤ)=(n:ℤ)+1 := by norm_cast
    rw [hcast]
    by_cases he : (z+(n:ℤ)+1)%2=0
    · have he1 : (z-1+(n:ℤ))%2=0 := by omega
      have he2 : (z+1+(n:ℤ))%2=0 := by omega
      have hd1 : (z-1+(n:ℤ))/2=(z+((n:ℤ)+1))/2-1 := by omega
      have hd2 : (z+1+(n:ℤ))/2=(z+((n:ℤ)+1))/2 := by omega
      have he' : (z+((n:ℤ)+1))%2=0 := by omega
      simp only [he1,he2,he',ite_true,hd1,hd2,chooseInt_pascal,pow_succ]
      ring
    · have he1 : (z-1+(n:ℤ))%2≠0 := by omega
      have he2 : (z+1+(n:ℤ))%2≠0 := by omega
      have he' : (z+((n:ℤ)+1))%2≠0 := by omega
      simp [he1,he2,he']

lemma chooseInt_adjacent (n : ℕ) (k : ℤ) (hk : 0≤k) :
    ((k:ℝ)+1)*chooseInt n (k+1)=((n:ℝ)-k)*chooseInt n k := by
  have hc : (k+1).toNat=k.toNat+1 := by omega
  simp only [chooseInt,hk,show 0≤k+1 by omega,ite_true,hc]
  have hcast : (k.toNat:ℝ)=(k:ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk
  by_cases hn : k.toNat≤n
  · have he := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq n k.toNat)
    push_cast [Nat.cast_sub hn] at he
    rw [hcast] at he
    nlinarith
  · rw [Nat.choose_eq_zero_of_lt (by omega : n<k.toNat),
      Nat.choose_eq_zero_of_lt (by omega : n<k.toNat+1)]
    simp

lemma kernel_adjacent (n b : ℕ) :
    ((n:ℝ)+b+2)*kernel n ((b:ℤ)+2)=((n:ℝ)-b)*kernel n b := by
  rw [kernel_binomial,kernel_binomial]
  by_cases he : ((b:ℤ)+n)%2=0
  · have he' : ((b:ℤ)+2+n)%2=0 := by omega
    have hd : ((b:ℤ)+2+n)/2=((b:ℤ)+n)/2+1 := by omega
    rw [ite_eq_left he,ite_eq_left he',hd]
    have hk : 0≤((b:ℤ)+n)/2 := by omega
    have hc := chooseInt_adjacent n (((b:ℤ)+n)/2) hk
    have hr : 2*(((b:ℤ)+n)/2:ℤ)=(b:ℤ)+n := by omega
    have hr' : 2*((((b:ℤ)+n)/2:ℤ):ℝ)=(b:ℝ)+n := by exact_mod_cast hr
    have h1 : (n:ℝ)+b+2=2*((((b:ℤ)+n)/2:ℤ):ℝ)+2 := by linarith
    have h2 : (n:ℝ)-b=2*((n:ℝ)-((((b:ℤ)+n)/2:ℤ):ℝ)) := by linarith
    rw [h1,h2]
    rw [← mul_div_assoc,← mul_div_assoc]
    congr 1
    nlinarith
  · have he' : ((b:ℤ)+2+n)%2≠0 := by omega
    simp only [he,he',ite_false,mul_zero]

/-- Exact entrance density, including the zero-time and unreachable cases. -/
theorem killed_entrance (n b : ℕ) :
    killed n 0 b = (2*((b:ℝ)+1)/((n:ℝ)+b+2))*kernel n b := by
  rw [killed_reflection]
  simp only [Nat.cast_zero,sub_zero,add_zero]
  have he := kernel_adjacent n b
  have hp : (0:ℝ)<n+b+2 := by positivity
  field_simp
  nlinarith

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def sign (s : Bool) : ℤ := if s then 1 else -1

abbrev Path (n : ℕ) := Fin n → Bool

def pathSum {n : ℕ} (d : Path n) (k : ℕ) : ℤ :=
  ∑ i : Fin n, if i.val<k then sign (d i) else 0

@[simp] lemma pathSum_zero {n : ℕ} (d : Path n) : pathSum d 0=0 := by simp [pathSum]

lemma pathSum_cons {n : ℕ} (s : Bool) (d : Path n) (k : ℕ) :
    pathSum (Fin.cons s d) (k+1)=sign s+pathSum d k := by
  simp [pathSum,Fin.sum_univ_succ]

def splitPath (n : ℕ) : Path (n+1) ≃ Bool × Path n where
  toFun d := (d 0,Fin.tail d)
  invFun d := Fin.cons d.1 d.2
  left_inv d := by ext i; exact Fin.cases (by simp) (fun j => rfl) i
  right_inv d := by ext <;> simp

lemma sum_path_succ (n : ℕ) (F : Path (n+1) → ℝ) :
    (∑ d,F d)=(∑ d : Path n,F (Fin.cons true d))+(∑ d : Path n,F (Fin.cons false d)) := by
  rw [Fintype.sum_equiv (splitPath n) F (fun d => F (Fin.cons d.1 d.2)) (by intro d; simp [splitPath])]
  rw [Fintype.sum_prod_type,Fintype.sum_bool]

/-- Uniform nearest-neighbour path counting probability. -/
def pathMass (n : ℕ) (P : Path n → Prop) : ℝ :=
  (∑ d : Path n, if P d then (1:ℝ) else 0)/(2:ℝ)^n

lemma pathMass_congr {n : ℕ} {P Q : Path n → Prop} (h : ∀ d,P d↔Q d) :
    pathMass n P=pathMass n Q := by congr 2; funext d; rw [h d]

lemma pathMass_succ (n : ℕ) (P : Path (n+1) → Prop) :
    pathMass (n+1) P=(pathMass n (fun d => P (Fin.cons true d))+
      pathMass n (fun d => P (Fin.cons false d)))/2 := by
  unfold pathMass
  rw [sum_path_succ,pow_succ]
  ring

lemma pathMass_endpoint (n : ℕ) (z : ℤ) :
    pathMass n (fun d => pathSum d n=z)=kernel n z := by
  induction n generalizing z with
  | zero => simp [pathMass,pathSum,kernel,eq_comm]
  | succ n ih =>
    rw [pathMass_succ]
    have h1 : pathMass n (fun d => pathSum (Fin.cons true d) (n+1)=z)=
        pathMass n (fun d => pathSum d n=z-1) := by
      apply pathMass_congr; intro d; rw [pathSum_cons]; simp only [sign,ite_true]; omega
    have h2 : pathMass n (fun d => pathSum (Fin.cons false d) (n+1)=z)=
        pathMass n (fun d => pathSum d n=z+1) := by
      apply pathMass_congr; intro d; rw [pathSum_cons]; simp [sign]; omega
    rw [h1,h2,ih,ih,kernel_succ]

def nonnegativePath {n : ℕ} (a : ℤ) (d : Path n) : Prop :=
  ∀ k≤n, 0≤a+pathSum d k

lemma nonnegativePath_cons {n : ℕ} (a : ℤ) (s : Bool) (d : Path n) :
    nonnegativePath a (Fin.cons s d) ↔ 0≤a ∧ nonnegativePath (a+sign s) d := by
  constructor
  · intro h
    constructor
    · simpa using h 0 (by omega)
    · intro k hk
      have hh := h (k+1) (by omega)
      rw [pathSum_cons] at hh
      linarith
  · rintro ⟨ha,h⟩ k hk
    cases k with
    | zero => simpa using ha
    | succ k => rw [pathSum_cons]; have hh := h k (by omega); linarith

lemma pathMass_killed (n a b : ℕ) :
    pathMass n (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b)=killed n a b := by
  induction n generalizing a with
  | zero =>
    have h : ∀ d : Path 0,(nonnegativePath (a:ℤ) d ∧ (a:ℤ)+pathSum d 0=b) ↔ a=b := by
      intro d; simp [nonnegativePath,pathSum]
    rw [pathMass_congr h]
    simp [pathMass,killed]
  | succ n ih =>
    rw [pathMass_succ]
    have h1 : pathMass n (fun d => nonnegativePath a (Fin.cons true d) ∧
        (a:ℤ)+pathSum (Fin.cons true d) (n+1)=b)=
        pathMass n (fun d => nonnegativePath (a+1:ℕ) d ∧ ((a+1:ℕ):ℤ)+pathSum d n=b) := by
      apply pathMass_congr; intro d
      rw [nonnegativePath_cons,pathSum_cons]
      simp [sign,add_assoc]
    rw [h1,ih]
    cases a with
    | zero =>
      have h2 : pathMass n (fun d => nonnegativePath (0:ℤ) (Fin.cons false d) ∧
          (0:ℤ)+pathSum (Fin.cons false d) (n+1)=b)=0 := by
        have hh : ∀ d : Path n,¬nonnegativePath (0:ℤ) (Fin.cons false d) := by
          intro d h
          have hh := h 1 (by omega)
          norm_num [pathSum_cons,sign] at hh
        simp only [pathMass,hh,false_and,ite_false,Finset.sum_const_zero,zero_div]
      simp only [Nat.cast_zero] at *
      rw [h2]
      simp [killed]
    | succ a =>
      have h2 : pathMass n (fun d => nonnegativePath (a+1:ℕ) (Fin.cons false d) ∧
          ((a+1:ℕ):ℤ)+pathSum (Fin.cons false d) (n+1)=b)=
          pathMass n (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b) := by
        apply pathMass_congr; intro d
        rw [nonnegativePath_cons,pathSum_cons]
        simp [sign,add_assoc]
        omega
      rw [h2,ih]
      simp only [killed]
      ring

/-- Reflection counts actual nonnegative paths, including all parity cases. -/
theorem pathMass_reflection (n a b : ℕ) :
    pathMass n (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b)=
      kernel n ((b:ℤ)-a)-kernel n ((b:ℤ)+a+2) := by
  rw [pathMass_killed,killed_reflection]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

def binaryMass (k : ℕ) : ℝ := (if k=0 then 1/2 else 0)+(if k=2 then 1/2 else 0)

lemma binaryMass_nonneg (k : ℕ) : 0≤binaryMass k := by
  unfold binaryMass; positivity
lemma binaryMass_total : HasSum binaryMass 1 := by
  change HasSum (fun k : ℕ => (if k=0 then (1/2:ℝ) else 0)+(if k=2 then 1/2 else 0)) 1
  convert (hasSum_ite_eq (0:ℕ) (1/2:ℝ)).add (hasSum_ite_eq (2:ℕ) (1/2:ℝ)) using 1
  norm_num
lemma binaryMass_moment (r : ℕ) (hr : 0<r) :
    HasSum (fun k : ℕ => (k:ℝ)^r*binaryMass k) ((2:ℝ)^r/2) := by
  have he : (fun k : ℕ => (k:ℝ)^r*binaryMass k)=
      (fun k : ℕ => if k=2 then (2:ℝ)^r/2 else 0) := by
    funext k
    by_cases h0 : k=0
    · subst k; simp [binaryMass,zero_pow (by omega : r≠0)]
    · by_cases h2 : k=2
      · subst k; simp [binaryMass,div_eq_mul_inv]
      · simp [binaryMass,h0,h2]
  rw [he]
  exact hasSum_ite_eq (2:ℕ) _

def binaryOffspring : CriticalEvenOffspring where
  mass := binaryMass
  nonneg := binaryMass_nonneg
  total := binaryMass_total
  even_support k hk := by
    have h0 : k≠0 := by rintro rfl; norm_num at hk
    have h2 : k≠2 := by rintro rfl; norm_num at hk
    simp [binaryMass,h0,h2]
  zero_pos := by norm_num [binaryMass]
  two_pos := by norm_num [binaryMass]
  mean := by simpa using binaryMass_moment 1 (by omega)
  second := (binaryMass_moment 2 (by omega)).summable

@[simp] lemma binaryOffspring_variance : binaryOffspring.variance=1 := by
  unfold CriticalEvenOffspring.variance
  have he : (fun k : ℕ => ((k:ℝ)-1)^2*binaryOffspring.mass k)=binaryMass := by
    funext k
    by_cases h0 : k=0
    · subst k; norm_num [binaryOffspring,binaryMass]
    · by_cases h2 : k=2
      · subst k; norm_num [binaryOffspring,binaryMass]
      · simp [binaryOffspring,binaryMass,h0,h2]
  rw [he,binaryMass_total.tsum_eq]

@[simp] lemma binaryOffspring_sigma : binaryOffspring.sigma=1 := by
  simp [CriticalEvenOffspring.sigma]

/-- Binary paths really sample critical, variance-one even offspring. -/
def binaryDegree (s : Bool) : ℕ := if s then 2 else 0

instance : MeasurableSpace Bool := ⊤
instance : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

def coinLaw : Measure Bool := (2:ℝ≥0∞)⁻¹ • Measure.count

lemma coinLaw_singleton (s : Bool) : coinLaw {s}=(2:ℝ≥0∞)⁻¹ := by
  simp [coinLaw]

instance : IsProbabilityMeasure coinLaw := by
  constructor
  norm_num [coinLaw,Measure.count_apply_finite]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

lemma binaryDegree_preserving : MeasurePreserving binaryDegree coinLaw binaryOffspring.law.toMeasure := by
  refine ⟨measurable_of_countable _,?_⟩
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton k),
    binaryOffspring.law_singleton]
  by_cases h0 : k=0
  · subst k
    have he : binaryDegree ⁻¹' {0}={false} := by ext s; cases s <;> simp [binaryDegree]
    rw [he,coinLaw_singleton]
    norm_num [binaryOffspring,binaryMass,ENNReal.ofReal_div_of_pos]
  · by_cases h2 : k=2
    · subst k
      have he : binaryDegree ⁻¹' {2}={true} := by ext s; cases s <;> simp [binaryDegree]
      rw [he,coinLaw_singleton]
      norm_num [binaryOffspring,binaryMass,ENNReal.ofReal_div_of_pos]
    · have he : binaryDegree ⁻¹' {k}=∅ := by ext s; cases s <;> simp [binaryDegree,Ne.symm h0,Ne.symm h2]
      rw [he,measure_empty]
      simp [binaryOffspring,binaryMass,h0,h2]

lemma binaryStep (s : Bool) : ((binaryDegree s:ℕ):ℤ)-1=SimpleWalk.sign s := by
  cases s <;> norm_num [binaryDegree,SimpleWalk.sign]

def binaryArray {N : ℕ} (d : SimpleWalk.Path N) : Fin N → ℕ := fun i => binaryDegree (d i)

lemma binaryArray_preserving (N : ℕ) :
    MeasurePreserving (@binaryArray N) (Measure.pi (fun _ : Fin N => coinLaw))
      (binaryOffspring.iidLaw N) := by
  refine ⟨measurable_of_countable _,?_⟩
  change (Measure.pi _).map (fun d i => binaryDegree (d i))=Measure.pi _
  rw [Measure.pi_map_pi (fun _ => (measurable_of_countable binaryDegree).aemeasurable)]
  simp only [binaryDegree_preserving.map_eq]

lemma binaryArray_totalStep {N : ℕ} (d : SimpleWalk.Path N) :
    totalStep (binaryArray d)=SimpleWalk.pathSum d N := by
  simp [totalStep,binaryArray,binaryStep,SimpleWalk.pathSum]

lemma coinPath_singleton (N : ℕ) (d : SimpleWalk.Path N) :
    (Measure.pi (fun _ : Fin N => coinLaw)).real {d}=1/(2:ℝ)^N := by
  rw [measureReal_def,Measure.pi_singleton]
  simp only [coinLaw_singleton,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    ENNReal.toReal_pow,ENNReal.toReal_inv,ENNReal.toReal_ofNat]
  simp only [one_div,inv_pow]

lemma coinPath_event (N : ℕ) (P : SimpleWalk.Path N → Prop) :
    (Measure.pi (fun _ : Fin N => coinLaw)).real {d | P d}=SimpleWalk.pathMass N P := by
  classical
  have he : ({d | P d} : Set (SimpleWalk.Path N))=(Finset.univ.filter P : Finset _):= by ext; simp
  rw [he,← sum_measureReal_singleton]
  simp only [coinPath_singleton,Finset.sum_filter,SimpleWalk.pathMass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  split_ifs <;> simp

/-- The recursive symmetric kernel is the exact endpoint law used by the
already-proved finite-variance conditioned bridge invariance principle. -/
lemma binary_kernel (N : ℕ) (z : ℤ) :
    (binaryOffspring.iidLaw N).real {d | totalStep d=z}=SimpleWalk.kernel N z := by
  have hmap := (binaryArray_preserving N).map_eq
  rw [← hmap,measureReal_def,Measure.map_apply (measurable_of_countable _) (by measurability)]
  change (Measure.pi (fun _ : Fin N => coinLaw)).real {d | totalStep (binaryArray d)=z}=_
  simp_rw [binaryArray_totalStep]
  rw [coinPath_event,SimpleWalk.pathMass_endpoint]

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding
attribute [local instance] Classical.propDecidable

def arrayWalk {N : ℕ} (d : Fin N → ℕ) (k : ℕ) : ℤ :=
  ∑ i : Fin N, if i.val<k then ((d i:ℤ)-1) else 0

def ArrayGood {N : ℕ} (d : Fin N → ℕ) : Prop :=
  totalStep d= -1 ∧ ∀ k<N,0≤arrayWalk d k

lemma arrayWalk_codeEmbedding {N : ℕ} (d : Code N) (k : ℕ) :
    arrayWalk (codeEmbedding N d) k=walk d.val k := rfl

lemma arrayGood_range (N : ℕ) : {d : Fin N → ℕ | ArrayGood d}=Set.range (codeEmbedding N) := by
  ext d
  constructor
  · rintro ⟨hd,hpos⟩
    obtain ⟨b,hb⟩ := Set.mem_range.mp (show d∈Set.range (bridgeEmbedding N) from by
      rw [← totalStep_bridge_range]; exact hd)
    have hcode : IsTreeCode b.val := ⟨b.property,by
      intro k hk
      change 0≤arrayWalk (bridgeEmbedding N b) k
      rw [hb]
      exact hpos k hk⟩
    exact ⟨⟨b.val,hcode⟩,hb⟩
  · rintro ⟨d,rfl⟩
    exact ⟨totalStep_bridge ⟨d.val,d.property.1⟩,d.property.2⟩

/-- The actual good-array restriction is the weighted finite code sum. -/
lemma CriticalEvenOffspring.iid_good_integral (p : CriticalEvenOffspring) (N : ℕ)
    (F : (Fin N → ℕ) → ℝ) :
    (∫ d,if ArrayGood d then F d else 0 ∂p.iidLaw N)=
      ∑ d : Code N,codeWeight p d*F (codeEmbedding N d) := by
  let G : Code N → (Fin N → ℕ) → ℝ := fun c =>
    ({codeEmbedding N c} : Set (Fin N → ℕ)).indicator (fun _ => F (codeEmbedding N c))
  have hi (c : Code N) : Integrable (G c) (p.iidLaw N) :=
    (integrable_const _).indicator (measurableSet_singleton _)
  have he : (fun d => if ArrayGood d then F d else 0)=fun d => ∑ c : Code N,G c d := by
    funext d
    by_cases hd : ArrayGood d
    · obtain ⟨c,rfl⟩ := Set.mem_range.mp (show d∈Set.range (codeEmbedding N) from by
        rw [← arrayGood_range]; exact hd)
      rw [ite_eq_left hd,Finset.sum_eq_single c]
      · simp [G]
      · intro b _ hbc
        have hnot : codeEmbedding N c≠codeEmbedding N b := fun h => hbc ((codeEmbedding N).injective h.symm)
        simp [G,hnot]
      · simp
    · rw [ite_eq_right hd]
      symm
      apply Finset.sum_eq_zero
      intro c _
      have hn : d≠codeEmbedding N c := by
        intro he
        apply hd
        rw [← Set.mem_ofPred_eq (p := ArrayGood),arrayGood_range]
        exact ⟨c,he.symm⟩
      simp [G,hn]
  rw [he,integral_finsetSum _ (fun c _ => hi c)]
  apply Finset.sum_congr rfl
  intro c _
  dsimp only [G]
  rw [integral_indicator (measurableSet_singleton _),setIntegral_const,smul_eq_mul]
  rw [show (p.iidLaw N).real {codeEmbedding N c}=codeWeight p c from
    p.iid_bridge_singleton ⟨c.val,c.property.1⟩]

/-- No informal conditioning is used: finite code expectations are exactly
normalized restriction of the iid offspring law to the good event. -/
theorem CriticalEvenOffspring.code_iid_integral (p : CriticalEvenOffspring) (n : ℕ)
    (F : (Fin (2*n+1) → ℕ) → ℝ) :
    (∫ c,F (codeEmbedding (2*n+1) c) ∂p.codeLaw n)=
      (∫ d,if ArrayGood d then F d else 0 ∂p.iidLaw (2*n+1))/codePartition p (2*n+1) := by
  rw [p.code_integral,p.iid_good_integral,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

lemma arrayWalk_binaryArray {N : ℕ} (d : SimpleWalk.Path N) (k : ℕ) :
    arrayWalk (binaryArray d) k=SimpleWalk.pathSum d k := by
  simp [arrayWalk,binaryArray,binaryStep,SimpleWalk.pathSum]

def SimpleExcursion {N : ℕ} (d : SimpleWalk.Path N) : Prop :=
  SimpleWalk.pathSum d N= -1 ∧ ∀ k<N,0≤SimpleWalk.pathSum d k

lemma binaryArray_good {N : ℕ} (d : SimpleWalk.Path N) : ArrayGood (binaryArray d)↔SimpleExcursion d := by
  simp only [ArrayGood,SimpleExcursion,binaryArray_totalStep,arrayWalk_binaryArray]

lemma binary_partition (n : ℕ) :
    codePartition binaryOffspring (2*n+1)=SimpleWalk.kernel (2*n+1) (-1)/(2*n+1:ℕ) := by
  have h := codePartition_cyclic binaryOffspring (by omega : 0<2*n+1)
  rw [binaryOffspring.bridgePartition_eq_iid,binary_kernel] at h
  apply (eq_div_iff (by positivity : ((2*n+1:ℕ):ℝ)≠0)).mpr
  linarith

/-- Exact simple-excursion representation of the binary conditioned tree law. -/
theorem binary_code_integral (n : ℕ) (F : (Fin (2*n+1) → ℕ) → ℝ) :
    (∫ c,F (codeEmbedding (2*n+1) c) ∂binaryOffspring.codeLaw n)=
      ((2*n+1:ℕ):ℝ)/SimpleWalk.kernel (2*n+1) (-1) *
        ∫ d,if SimpleExcursion d then F (binaryArray d) else 0
          ∂Measure.pi (fun _ : Fin (2*n+1) => coinLaw) := by
  rw [binaryOffspring.code_iid_integral,binary_partition]
  rw [← (binaryArray_preserving (2*n+1)).map_eq,
    integral_map (measurable_of_countable _).aemeasurable (measurable_of_countable _).aestronglyMeasurable]
  simp_rw [binaryArray_good]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end FKCRT.TreeCoding
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

def splitPathAt (n m : ℕ) : Path (n+m) ≃ Path n × Path m where
  toFun d := (fun i => d (Fin.castAdd m i),fun i => d (Fin.natAdd n i))
  invFun d := Fin.append d.1 d.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv _ := by ext <;> simp

lemma pathSum_append_left {n m k : ℕ} (d : Path n) (e : Path m) (hk : k≤n) :
    pathSum (Fin.append d e) k=pathSum d k := by
  unfold pathSum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd]
  have hzero : ∑ i : Fin m, (if n+i.val<k then sign (e i) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by omega)]
  rw [hzero,add_zero]

lemma pathSum_append_right {n m : ℕ} (d : Path n) (e : Path m) (k : ℕ) :
    pathSum (Fin.append d e) (n+k)=pathSum d n+pathSum e k := by
  unfold pathSum
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left,Fin.append_right,Fin.val_castAdd,Fin.val_natAdd,
    Nat.add_lt_add_iff_left]
  have he : ∀ i : Fin n, (if i.val<n+k then sign (d i) else 0)=if i.val<n then sign (d i) else 0 :=
    fun i => by rw [ite_eq_left (by omega),ite_eq_left i.isLt]
  simp_rw [he]

lemma nonnegativePath_append {n m : ℕ} (a : ℤ) (d : Path n) (e : Path m) :
    nonnegativePath a (Fin.append d e) ↔
      nonnegativePath a d ∧ nonnegativePath (a+pathSum d n) e := by
  constructor
  · intro h
    constructor
    · intro k hk
      simpa only [pathSum_append_left d e hk] using h k (by omega)
    · intro k hk
      have hh := h (n+k) (by omega)
      rw [pathSum_append_right] at hh
      linarith
  · rintro ⟨hd,he⟩ k hk
    by_cases hkn : k≤n
    · rw [pathSum_append_left d e hkn]; exact hd k hkn
    · have hke : k=n+(k-n) := by omega
      rw [hke,pathSum_append_right]
      have hh := he (k-n) (by omega)
      linarith

lemma pathMass_append (n m : ℕ) (P : Path n → Prop) (Q : Path m → Prop) :
    pathMass (n+m) (fun d => P ((splitPathAt n m d).1) ∧ Q ((splitPathAt n m d).2))=
      pathMass n P*pathMass m Q := by
  unfold pathMass
  rw [Fintype.sum_equiv (splitPathAt n m) _
    (fun d => if P d.1 ∧ Q d.2 then (1:ℝ) else 0) (by intro d; split_ifs <;> rfl)]
  rw [Fintype.sum_prod_type]
  have he : ∀ d : Path n,∀ e : Path m,(if P d ∧ Q e then (1:ℝ) else 0)=
      (if P d then 1 else 0)*(if Q e then 1 else 0) := by
    intro d e; split_ifs <;> simp_all
  simp_rw [he,← Finset.mul_sum]
  rw [← Finset.sum_mul,pow_add]
  ring

/-- Exact fixed-middle-point Markov factorization of killed path counts. -/
theorem pathMass_killed_middle (n m a b c : ℕ) :
    pathMass (n+m) (fun d => nonnegativePath a d ∧
      (a:ℤ)+pathSum d n=b ∧ (a:ℤ)+pathSum d (n+m)=c)=
        killed n a b*killed m b c := by
  have he : ∀ d : Path (n+m),
      (nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b ∧ (a:ℤ)+pathSum d (n+m)=c)↔
      ((nonnegativePath a (splitPathAt n m d).1 ∧ (a:ℤ)+pathSum (splitPathAt n m d).1 n=b) ∧
      (nonnegativePath b (splitPathAt n m d).2 ∧ (b:ℤ)+pathSum (splitPathAt n m d).2 m=c)) := by
    intro d
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt n m).symm.surjective d
    simp only [Equiv.apply_symm_apply]
    change (nonnegativePath a (Fin.append d e) ∧ (a:ℤ)+pathSum (Fin.append d e) n=b ∧
      (a:ℤ)+pathSum (Fin.append d e) (n+m)=c)↔_
    simp only [nonnegativePath_append,pathSum_append_left d e le_rfl,pathSum_append_right]
    constructor
    · rintro ⟨⟨hd,he⟩,hb,hc⟩
      refine ⟨⟨hd,hb⟩,?_,?_⟩
      · rwa [hb] at he
      · linarith
    · rintro ⟨⟨hd,hb⟩,he,hc⟩
      refine ⟨⟨hd,?_⟩,hb,?_⟩
      · rwa [hb]
      · linarith
  rw [pathMass_congr he,pathMass_append n m
    (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b)
    (fun e => nonnegativePath b e ∧ (b:ℤ)+pathSum e m=c),pathMass_killed,pathMass_killed]

/-- Probability of a first visit to -1, starting at a nonnegative integer. -/
def firstHit {n : ℕ} (a : ℕ) (d : Path n) : Prop :=
  (a:ℤ)+pathSum d n= -1 ∧ ∀ k<n,0≤(a:ℤ)+pathSum d k

lemma firstHit_last {n : ℕ} (a : ℕ) (d : Path n) (s : Path 1) :
    firstHit a (Fin.append d s) ↔
      nonnegativePath a d ∧ (a:ℤ)+pathSum d n=0 ∧ s 0=false := by
  have hs : pathSum s 1=sign (s 0) := by simp [pathSum]
  simp only [firstHit,pathSum_append_right,hs]
  constructor
  · rintro ⟨hend,hpos⟩
    have hd : nonnegativePath a d := by
      intro k hk
      have hh := hpos k (by omega)
      rwa [pathSum_append_left d s hk] at hh
    have hn := hd n le_rfl
    have hb : s 0=false := by
      cases h : s 0 <;> simp_all [sign]
      omega
    refine ⟨hd,?_,hb⟩
    rw [hb] at hend
    norm_num [sign] at hend
    linarith
  · rintro ⟨hd,he,hb⟩
    constructor
    · rw [hb]; norm_num [sign]; linarith
    · intro k hk
      rw [pathSum_append_left d s (by omega)]
      exact hd k (by omega)

lemma pathMass_firstHit (n a : ℕ) :
    pathMass (n+1) (firstHit a)=killed n a 0/2 := by
  have he : ∀ d : Path (n+1), firstHit a d↔
      (nonnegativePath a (splitPathAt n 1 d).1 ∧ (a:ℤ)+pathSum (splitPathAt n 1 d).1 n=0) ∧
      (splitPathAt n 1 d).2 0=false := by
    intro d
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt n 1).symm.surjective d
    simp only [Equiv.apply_symm_apply]
    change firstHit a (Fin.append d e)↔_
    simpa only [and_assoc] using firstHit_last a d e
  rw [pathMass_congr he,pathMass_append n 1
    (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d n=0) (fun s => s 0=false)]
  have hlast : pathMass 1 (fun s => s 0=false)=1/2 := by
    rw [pathMass_succ]
    norm_num [pathMass]
  rw [hlast]
  have hk := pathMass_killed n a 0
  norm_num only [Nat.cast_zero] at hk
  rw [hk]
  ring

/-- Ballot/first-hitting formula, without parity or reachability restrictions. -/
theorem firstHit_formula (n a : ℕ) :
    pathMass (n+1) (firstHit a)=((a:ℝ)+1)/((n:ℝ)+1)*kernel (n+1) ((a:ℤ)+1) := by
  rw [pathMass_firstHit,killed_symm,killed_entrance,kernel_succ]
  rw [show (a:ℤ)+1-1=a by ring,show (a:ℤ)+1+1=a+2 by ring]
  have h := kernel_adjacent n a
  have hn : (n:ℝ)+1≠0 := by positivity
  have ha : (n:ℝ)+a+2≠0 := by positivity
  field_simp
  nlinarith

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
attribute [local instance] Classical.propDecidable

lemma pathMass_true (n : ℕ) : pathMass n (fun _ => True)=1 := by
  simp [pathMass]

lemma pathMass_endpoint_from (n : ℕ) (a b : ℤ) :
    pathMass n (fun d => a+pathSum d n=b)=kernel n (b-a) := by
  have he : ∀ d : Path n, (a+pathSum d n=b)↔pathSum d n=b-a := by
    intro d; omega
  rw [pathMass_congr he,pathMass_endpoint]

/-- Cutting a first-hitting path at a specified nonnegative intermediate level. -/
lemma firstHit_append_middle {n m : ℕ} (a b : ℕ) (d : Path n) (e : Path m) :
    (firstHit a (Fin.append d e) ∧ (a:ℤ)+pathSum d n=b)↔
      (nonnegativePath a d ∧ (a:ℤ)+pathSum d n=b) ∧ firstHit b e := by
  constructor
  · rintro ⟨⟨hend,hpos⟩,hb⟩
    have hd : nonnegativePath a d := by
      intro k hk
      by_cases he : k=n
      · subst k; omega
      · have hh := hpos k (by omega)
        rwa [pathSum_append_left d e hk] at hh
    refine ⟨⟨hd,hb⟩,?_,?_⟩
    · rw [pathSum_append_right] at hend
      linarith
    · intro k hk
      have hh := hpos (n+k) (by omega)
      rw [pathSum_append_right] at hh
      linarith
  · rintro ⟨⟨hd,hb⟩,hend,hpos⟩
    refine ⟨⟨?_,?_⟩,hb⟩
    · rw [pathSum_append_right]; linarith
    · intro k hk
      by_cases hkn : k≤n
      · rw [pathSum_append_left d e hkn]; exact hd k hkn
      · have hke : k=n+(k-n) := by omega
        rw [hke,pathSum_append_right]
        have hh := hpos (k-n) (by omega)
        linarith

def traceSize (R : ℕ) : List (ℕ×ℕ) → ℕ
  | [] => R
  | x::xs => x.1+traceSize R xs

/-- Successive specified heights, with free terminal suffix. -/
def tracePoints (a R : ℕ) : (xs : List (ℕ×ℕ)) → Path (traceSize R xs) → Prop
  | [],_ => True
  | x::xs,d => (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2 ∧
    tracePoints x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2

/-- The same specified heights, together with nonnegative segments and final first hit. -/
def traceExcursion (a R : ℕ) : (xs : List (ℕ×ℕ)) → Path (traceSize R xs) → Prop
  | [],d => firstHit a d
  | x::xs,d =>
    (nonnegativePath a (splitPathAt x.1 (traceSize R xs) d).1 ∧
      (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2) ∧
    traceExcursion x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2

def traceFreeWeight (a : ℕ) : List (ℕ×ℕ) → ℝ
  | [] => 1
  | x::xs => kernel x.1 ((x.2:ℤ)-a)*traceFreeWeight x.2 xs

def traceKilledWeight (a R : ℕ) : List (ℕ×ℕ) → ℝ
  | [] => pathMass R (firstHit a)
  | x::xs => killed x.1 a x.2*traceKilledWeight x.2 R xs

lemma traceExcursion_iff (a R : ℕ) (xs : List (ℕ×ℕ)) (d : Path (traceSize R xs)) :
    traceExcursion a R xs d↔firstHit a d ∧ tracePoints a R xs d := by
  induction xs generalizing a with
  | nil => simp only [traceExcursion,tracePoints,and_true]
  | cons x xs ih =>
    obtain ⟨⟨d,e⟩,rfl⟩ := (splitPathAt x.1 (traceSize R xs)).symm.surjective d
    simp only [traceExcursion,tracePoints,Equiv.apply_symm_apply,ih]
    change ((nonnegativePath a d ∧ (a:ℤ)+pathSum d x.1=x.2) ∧ firstHit x.2 e ∧
        tracePoints x.2 R xs e)↔
      firstHit a (Fin.append d e) ∧ ((a:ℤ)+pathSum d x.1=x.2) ∧ tracePoints x.2 R xs e
    have hh := firstHit_append_middle a x.2 d e
    tauto

/-- Actual unrestricted finite-dimensional probabilities factor into free kernels. -/
theorem pathMass_tracePoints (a R : ℕ) (xs : List (ℕ×ℕ)) :
    pathMass (traceSize R xs) (tracePoints a R xs)=traceFreeWeight a xs := by
  induction xs generalizing a with
  | nil => exact pathMass_true R
  | cons x xs ih =>
    change pathMass (x.1+traceSize R xs) (fun d =>
      ((a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2) ∧
      tracePoints x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2)=_
    rw [pathMass_append x.1 (traceSize R xs) (fun d => (a:ℤ)+pathSum d x.1=x.2)
      (tracePoints x.2 R xs),pathMass_endpoint_from,ih]
    rfl

/-- Actual nonnegative first-hitting finite-dimensional probabilities have the
reflected-kernel product, with the exact terminal first-hitting factor. -/
theorem pathMass_traceExcursion (a R : ℕ) (xs : List (ℕ×ℕ)) :
    pathMass (traceSize R xs) (traceExcursion a R xs)=traceKilledWeight a R xs := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    change pathMass (x.1+traceSize R xs) (fun d =>
      (nonnegativePath a (splitPathAt x.1 (traceSize R xs) d).1 ∧
      (a:ℤ)+pathSum (splitPathAt x.1 (traceSize R xs) d).1 x.1=x.2) ∧
      traceExcursion x.2 R xs (splitPathAt x.1 (traceSize R xs) d).2)=_
    rw [pathMass_append x.1 (traceSize R xs)
      (fun d => nonnegativePath a d ∧ (a:ℤ)+pathSum d x.1=x.2)
      (traceExcursion x.2 R xs),pathMass_killed,ih]
    rfl

lemma killed_le_kernel (n a b : ℕ) : killed n a b≤kernel n ((b:ℤ)-a) := by
  rw [killed_reflection]
  exact sub_le_self _ (kernel_nonneg _ _)

lemma traceKilledWeight_nonneg (a R : ℕ) (xs : List (ℕ×ℕ)) :
    0≤traceKilledWeight a R xs := by
  rw [← pathMass_traceExcursion]
  unfold pathMass
  positivity

lemma traceFreeWeight_nonneg (a : ℕ) (xs : List (ℕ×ℕ)) : 0≤traceFreeWeight a xs := by
  induction xs generalizing a with
  | nil => norm_num [traceFreeWeight]
  | cons x xs ih => exact mul_nonneg (kernel_nonneg _ _) (ih _)

lemma traceKilledWeight_eq_zero (a R : ℕ) (xs : List (ℕ×ℕ))
    (h : traceFreeWeight a xs=0) : traceKilledWeight a R xs=0 := by
  induction xs generalizing a with
  | nil => norm_num [traceFreeWeight] at h
  | cons x xs ih =>
    change kernel x.1 ((x.2:ℤ)-a)*traceFreeWeight x.2 xs=0 at h
    rcases mul_eq_zero.mp h with h | h
    · have hk : killed x.1 a x.2=0 := le_antisymm (by simpa only [h] using killed_le_kernel x.1 a x.2)
        (killed_nonneg _ _ _)
      simp [traceKilledWeight,hk]
    · simp [traceKilledWeight,ih _ h]

end FKCRT.SimpleWalk
end


noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.SimpleWalk
open TreeCoding
attribute [local instance] Classical.propDecidable

-- The inherited product-law realization, not a fresh informal conditioning.
def uniformLaw (N : ℕ) : Measure (Path N) := Measure.pi (fun _ => coinLaw)

instance uniformLaw_probability (N : ℕ) : IsProbabilityMeasure (uniformLaw N) := inferInstanceAs
  (IsProbabilityMeasure (Measure.pi (fun _ : Fin N => coinLaw)))

lemma uniformLaw_singleton (N : ℕ) (d : Path N) :
    (uniformLaw N).real {d}=1/(2:ℝ)^N := by
  rw [measureReal_def,uniformLaw,Measure.pi_singleton]
  simp [coinLaw]

lemma uniformLaw_real (N : ℕ) (A : Set (Path N)) :
    (uniformLaw N).real A=pathMass N (fun d => d∈A) := by
  classical
  have he : ((Finset.univ.filter (fun d => d∈A) : Finset (Path N)) : Set (Path N))=A := by
    ext d; simp
  rw [← he,← sum_measureReal_singleton]
  simp only [Finset.sum_filter,uniformLaw_singleton,pathMass,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp

lemma firstHit_zero_iff {N : ℕ} (d : Path N) : firstHit 0 d↔SimpleExcursion d := by
  simp [firstHit,SimpleExcursion]

lemma firstHit_mass_pos (n : ℕ) : 0<pathMass (2*n+1) (firstHit 0) := by
  rw [firstHit_formula]
  norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add,one_mul]
  rw [← kernel_symm (2*n+1) 1]
  have h := codePartition_odd_pos binaryOffspring n
  rw [binary_partition] at h
  convert h using 1
  push_cast
  ring

/-- Uniform binary walks conditioned on their first hit of -1 at the odd endpoint. -/
def excursionLaw (n : ℕ) : Measure (Path (2*n+1)) :=
  cond (uniformLaw (2*n+1)) {d | firstHit 0 d}

instance excursionLaw_probability (n : ℕ) : IsProbabilityMeasure (excursionLaw n) := by
  apply cond_isProbabilityMeasure
  intro h
  have hp := firstHit_mass_pos n
  change 0<pathMass (2*n+1) (fun d => d∈{d | firstHit 0 d}) at hp
  rw [← uniformLaw_real] at hp
  simp only [measureReal_def,h,ENNReal.toReal_zero,lt_self_iff_false] at hp

lemma excursionLaw_real (n : ℕ) (A : Set (Path (2*n+1))) :
    (excursionLaw n).real A=
      pathMass (2*n+1) (fun d => firstHit 0 d ∧ d∈A)/pathMass (2*n+1) (firstHit 0) := by
  rw [measureReal_def,excursionLaw,cond_apply ((Set.to_countable _).measurableSet),
    ENNReal.toReal_mul,ENNReal.toReal_inv]
  change ((uniformLaw (2*n+1)).real {d | firstHit 0 d})⁻¹ *
    (uniformLaw (2*n+1)).real ({d | firstHit 0 d}∩A)=_
  rw [uniformLaw_real,uniformLaw_real]
  simp only [mem_inter_iff,mem_ofPred_eq,div_eq_mul_inv,mul_comm]

lemma excursionLaw_ae (n : ℕ) : ∀ᵐ d ∂excursionLaw n,firstHit 0 d :=
  ae_cond_mem₀ ((Set.to_countable _).measurableSet.nullMeasurableSet)

lemma excursionLaw_integral (n : ℕ) (F : Path (2*n+1) → ℝ) :
    (∫ d,F d ∂excursionLaw n)=
      (∫ d,if firstHit 0 d then F d else 0 ∂uniformLaw (2*n+1))/
        pathMass (2*n+1) (firstHit 0) := by
  rw [excursionLaw,TreeCoding.integral_cond_eq_div _ _ ((Set.to_countable _).measurableSet),uniformLaw_real]
  rfl

lemma binary_code_integral (n : ℕ) (F : (Fin (2*n+1) → ℕ) → ℝ) :
    (∫ c,F (codeEmbedding (2*n+1) c) ∂binaryOffspring.codeLaw n)=
      ∫ d,F (binaryArray d) ∂excursionLaw n := by
  rw [binaryOffspring.code_iid_integral,excursionLaw_integral]
  have hn : codePartition binaryOffspring (2*n+1)=pathMass (2*n+1) (firstHit 0) := by
    rw [binary_partition,firstHit_formula]
    norm_num only [Nat.cast_zero,Int.natCast_zero,zero_add,one_mul]
    rw [← kernel_symm (2*n+1) 1]
    push_cast
    ring
  rw [hn,← (binaryArray_preserving (2*n+1)).map_eq,
    integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with d
  simp only [binaryArray_good,← firstHit_zero_iff]

lemma pathSum_parity {N : ℕ} (d : Path N) {k : ℕ} (hk : k≤N) :
    Even (pathSum d k-(k:ℤ)) := by
  induction N generalizing k with
  | zero =>
    have : k=0 := by omega
    subst k
    simp
  | succ N ih =>
    cases k with
    | zero => simp
    | succ k =>
      have he : d=Fin.cons (d 0) (Fin.tail d) := (Fin.cons_self_tail d).symm
      rw [he,pathSum_cons]
      have hh := ih (Fin.tail d) (by omega : k≤N)
      have hs : Even (sign (d 0)-1) := by cases d 0 <;> norm_num [sign]
      have heq : sign (d 0)+pathSum (Fin.tail d) k-((k+1:ℕ):ℤ)=
          (sign (d 0)-1)+(pathSum (Fin.tail d) k-(k:ℤ)) := by push_cast; ring
      rw [heq]
      exact hs.add hh

end FKCRT.SimpleWalk
end

end OAI
