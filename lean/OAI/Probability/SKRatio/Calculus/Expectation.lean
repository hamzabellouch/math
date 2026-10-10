import Mathlib
import OAI.Probability.SKRatio.Calculus.TwoSpin

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

@[simp] lemma spinValue_true : spinValue true = 1 := rfl
@[simp] lemma spinValue_false : spinValue false = -1 := rfl
@[simp] lemma spinValue_not (b : Bool) : spinValue (!b) = -spinValue b := by
  cases b <;> norm_num [spinValue]

lemma abs_tanh_lt_one (a : ℝ) : |tanh a| < 1 :=
  abs_lt.mpr ⟨Real.neg_one_lt_tanh a, Real.tanh_lt_one a⟩

lemma sum_flip (i : Fin n) (F : Spin n → ℝ) : ∑ x, F (flip i x) = ∑ x, F x :=
  Equiv.sum_comp (Function.Involutive.toPerm (flip i) (flip_flip i)) F

def expectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ x, mass g h x * f x

def variance {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  expectation g h (fun x => (f x - expectation g h f) ^ 2)

def conditionalExpectation {n : ℕ} (g : Disorder n) (h : Fin n → ℝ)
    (i : Fin n) (f : Spin n → ℝ) (x : Spin n) : ℝ :=
  (weight g h x * f x + weight g h (flip i x) * f (flip i x)) /
    (weight g h x + weight g h (flip i x))

def dirichlet {n : ℕ} (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) : ℝ :=
  ∑ i, expectation g h (fun x => (f x - conditionalExpectation g h i f x) ^ 2)

@[simp] theorem expectation_const (g : Disorder n) (h : Fin n → ℝ) (c : ℝ) :
    expectation g h (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul]

theorem expectation_add (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x + k x) = expectation g h f + expectation g h k := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_sub (g : Disorder n) (h : Fin n → ℝ) (f k : Spin n → ℝ) :
    expectation g h (fun x => f x - k x) = expectation g h f - expectation g h k := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

theorem expectation_mul_const (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => f x * c) = expectation g h f * c := by
  simp only [expectation, Finset.sum_mul, mul_assoc]

theorem expectation_const_mul (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) (c : ℝ) :
    expectation g h (fun x => c * f x) = c * expectation g h f := by
  simp only [mul_comm c, expectation_mul_const]

theorem expectation_nonneg (g : Disorder n) (h : Fin n → ℝ) {f : Spin n → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ expectation g h f :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (mass_nonneg g h x) (hf x))

theorem variance_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ variance g h f := expectation_nonneg g h (fun _ => sq_nonneg _)

theorem dirichlet_nonneg (g : Disorder n) (h : Fin n → ℝ) (f : Spin n → ℝ) :
    0 ≤ dirichlet g h f :=
  Finset.sum_nonneg (fun _ _ => expectation_nonneg g h (fun _ => sq_nonneg _))

lemma conditionalExpectation_flip (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f (flip i x)=conditionalExpectation g h i f x := by
  simp only [conditionalExpectation,flip_flip]
  rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma conditionalExpectation_idem (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (conditionalExpectation g h i f) x=conditionalExpectation g h i f x := by
  unfold conditionalExpectation at *
  rw [flip_flip]
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hd' : weight g h (flip i x)+weight g h x ≠ 0 := by simpa only [add_comm] using hd
  field_simp [hd,hd']
  ring

lemma expectation_flip_average (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (F : Spin n→ℝ) :
    expectation g h F=(1/2)*∑ x,(mass g h x*F x+mass g h (flip i x)*F (flip i x)) := by
  rw [Finset.sum_add_distrib,sum_flip i (fun x=>mass g h x*F x)]
  unfold expectation
  ring

lemma conditionalExpectation_adjoint (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) :
    expectation g h (fun x=>conditionalExpectation g h i f x*k x)=
    expectation g h (fun x=>f x*conditionalExpectation g h i k x) := by
  rw [expectation_flip_average g h i,expectation_flip_average g h i]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [conditionalExpectation_flip,conditionalExpectation_flip]
  unfold mass conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hZ := (partition_pos g h).ne'
  field_simp [hd,hZ]

lemma conditionalExpectation_mul_invariant (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (hk : ∀ x,k (flip i x)=k x) (x : Spin n) :
    conditionalExpectation g h i (fun x=>f x*k x) x=conditionalExpectation g h i f x*k x := by
  unfold conditionalExpectation
  dsimp only
  rw [hk]
  ring

lemma conditionalExpectation_const (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (x : Spin n) : conditionalExpectation g h i (fun _=>c) x=c := by
  unfold conditionalExpectation
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  field_simp [hd]

lemma expectation_conditionalExpectation (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) : expectation g h (conditionalExpectation g h i f)=expectation g h f := by
  have he := conditionalExpectation_adjoint g h i f (fun _=>1)
  simpa only [conditionalExpectation_const,mul_one] using he

lemma expectation_projection_square (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>f x*(f x-conditionalExpectation g h i f x)) := by
  have he := conditionalExpectation_adjoint g h i f (conditionalExpectation g h i f)
  simp only [conditionalExpectation_idem] at he
  have hp (x : Spin n) : (f x-conditionalExpectation g h i f x)^2=
      f x*(f x-conditionalExpectation g h i f x)+
      (conditionalExpectation g h i f x*conditionalExpectation g h i f x-
        f x*conditionalExpectation g h i f x) := by ring
  simp_rw [hp]
  rw [expectation_add,expectation_sub,he]
  ring

def heatBathGenerator (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  ∑ i,(f x-conditionalExpectation g h i f x)

lemma expectation_sum (g : Disorder n) (h : Fin n→ℝ) {ι : Type*} [Fintype ι]
    (F : ι→Spin n→ℝ) : expectation g h (fun x=>∑ i,F i x)=∑ i,expectation g h (F i) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

lemma heatBathGenerator_form (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>f x*heatBathGenerator g h f x)=dirichlet g h f := by
  unfold heatBathGenerator dirichlet
  simp_rw [Finset.mul_sum]
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (expectation_projection_square g h i f).symm

lemma heatBathGenerator_adjoint (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x*k x)=
      expectation g h (fun x=>f x*heatBathGenerator g h k x) := by
  unfold heatBathGenerator
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [expectation_sum,expectation_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [sub_mul,mul_sub]
  rw [expectation_sub,expectation_sub,conditionalExpectation_adjoint]

lemma conditionalDifference_zero_iff (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) : f x-conditionalExpectation g h i f x=0 ↔ f x=f (flip i x) := by
  have hd : weight g h x+weight g h (flip i x) ≠ 0 := (add_pos (weight_pos _ _ _) (weight_pos _ _ _)).ne'
  have hw := (weight_pos g h (flip i x)).ne'
  unfold conditionalExpectation
  rw [sub_eq_zero,eq_div_iff hd]
  constructor
  · intro hh
    have he : weight g h (flip i x)*(f x-f (flip i x))=0 := by nlinarith only [hh]
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hw)
  · intro hh
    rw [hh]
    ring

lemma flip_invariant_constant (f : Spin n→ℝ) (hf : ∀ i x,f (flip i x)=f x) :
    ∀ x y,f x=f y := by
  classical
  intro x y
  have hs : ∀ S : Finset (Fin n),f (fun i=>if i∈S then y i else x i)=f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      let z : Spin n := fun k=>if k∈S then y k else x k
      have he : (fun k=>if k∈insert i S then y k else x k)=Function.update z i (y i) := by
        funext k
        by_cases hk : k=i
        · subst k;simp
        · simp [z,hk]
      rw [he]
      have hz : f (Function.update z i (y i))=f z := by
        by_cases hiy : y i=z i
        · rw [hiy,Function.update_eq_self]
        · have hnot : y i= !(z i) := by
            cases hy : y i <;> cases hz : z i <;> simp_all
          rw [hnot]
          exact hf i z
      exact hz.trans ih
  simpa using (hs Finset.univ).symm

lemma dirichlet_eq_zero_iff (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=0 ↔ ∀ x y,f x=f y := by
  constructor
  · intro hh
    have hi : ∀ i,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _=>expectation_nonneg g h (fun _=>sq_nonneg _))).mp hh i (Finset.mem_univ _)
    have hf : ∀ i x,f (flip i x)=f x := by
      intro i x
      have hx : mass g h x*(f x-conditionalExpectation g h i f x)^2=0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun y _=>mul_nonneg (mass_nonneg g h y) (sq_nonneg _))).mp
          (hi i) x (Finset.mem_univ _)
      have hd := (mul_eq_zero.mp hx).resolve_left (mass_pos g h x).ne'
      exact ((conditionalDifference_zero_iff g h i f x).mp (sq_eq_zero_iff.mp hd)).symm
    exact flip_invariant_constant f hf
  · intro hf
    unfold dirichlet
    apply Finset.sum_eq_zero
    intro i _
    have he : ∀ x,f x-conditionalExpectation g h i f x=0 := fun x=>(conditionalDifference_zero_iff g h i f x).mpr (hf x (flip i x))
    simp only [he,zero_pow (by omega : (2:ℕ) ≠ 0)]
    simp [expectation]

def localField (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  h i+∑ k,coupling g i k*spinValue (x k)
def spinGradient (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  (f (Function.update x i true)-f (Function.update x i false))/2

def realSpinEnergy (g : Disorder n) (h v : Fin n→ℝ) : ℝ :=
  (1/2)*(v ⬝ᵥ (Matrix.of (coupling g) *ᵥ v))+h ⬝ᵥ v

lemma realSpinEnergy_eq (g : Disorder n) (h : Fin n→ℝ) (x : Spin n) :
    realSpinEnergy g h (fun i=>spinValue (x i))=hamiltonian g h x := by
  unfold realSpinEnergy hamiltonian
  congr 1
  congr 1
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _;ring

lemma dot_coupling_single (g : Disorder n) (v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    v ⬝ᵥ (Matrix.of (coupling g) *ᵥ Pi.single i a)=a*(Matrix.of (coupling g) *ᵥ v) i := by
  rw [Matrix.mulVec_single]
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [coupling_symm g k i]
  ring

lemma realSpinEnergy_update (g : Disorder n) (h v : Fin n→ℝ) (i : Fin n) (a : ℝ) :
    realSpinEnergy g h (Function.update v i a)=realSpinEnergy g h v+
      (a-v i)*(h i+(Matrix.of (coupling g) *ᵥ v) i) := by
  have he : Function.update v i a=v+Pi.single i (a-v i) := by
    funext k
    by_cases hk : k=i
    · subst k;simp
    · simp [hk]
  rw [he]
  unfold realSpinEnergy
  rw [Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct,dotProduct_add,
    dot_coupling_single,single_dotProduct,single_dotProduct,dotProduct_single,Matrix.mulVec_single]
  simp only [Pi.smul_apply,op_smul_eq_mul,Matrix.col_apply,Matrix.of_apply,coupling_diag,zero_mul]
  ring

lemma spinValue_update (x : Spin n) (i : Fin n) (b : Bool) :
    (fun k=>spinValue (Function.update x i b k))=Function.update (fun k=>spinValue (x k)) i (spinValue b) := by
  funext k
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma hamiltonian_update (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    hamiltonian g h (Function.update x i b)=hamiltonian g h x+
      (spinValue b-spinValue (x i))*localField g h i x := by
  rw [← realSpinEnergy_eq,spinValue_update,realSpinEnergy_update,realSpinEnergy_eq]
  rfl

lemma localField_update_self (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x i b)=localField g h i x := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k=i
  · subst k;simp
  · simp [Function.update_of_ne hk]

lemma localField_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) (b : Bool) :
    localField g h i (Function.update x j b)=localField g h i x+
      coupling g i j*(spinValue b-spinValue (x j)) := by
  unfold localField
  have he : (fun k=>spinValue (Function.update x j b k))=
      (fun k=>spinValue (x k))+Pi.single j (spinValue b-spinValue (x j)) := by
    funext k
    by_cases hk : k=j
    · subst k;simp
    · simp [Function.update_of_ne hk,Pi.single_eq_of_ne hk]
  change h i+(coupling g i ⬝ᵥ (fun k=>spinValue (Function.update x j b k)))=_
  rw [he,dotProduct_add,dotProduct_single]
  exact (add_assoc _ _ _).symm

lemma exp_spin (t : ℝ) (x : Bool) :
    exp (t*spinValue x)=cosh t*(1+tanh t*spinValue x) := by
  have h : cosh t ≠ 0 := (cosh_pos t).ne'
  cases x
  · simp only [spinValue_false,mul_neg_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_sub_sinh]
    field_simp
    ring
  · simp only [spinValue_true,mul_one,tanh_eq_sinh_div_cosh]
    rw [← cosh_add_sinh]
    field_simp

lemma exp_spin_product (t : ℝ) (x y : Bool) :
    exp (t*spinValue x*spinValue y)=cosh t*(1+tanh t*spinValue x*spinValue y) := by
  cases y
  · simp only [spinValue_false,mul_neg_one]
    have he := exp_spin t (!x)
    simpa only [spinValue_not,mul_neg,neg_mul] using he
  · simpa only [spinValue_true,mul_one] using exp_spin t x

def pairBoltzmannWeight (α γ J : ℝ) (x y : Bool) : ℝ :=
  exp (α*spinValue x+γ*spinValue y+J*spinValue x*spinValue y)
def pairBoltzmannMean (α γ J : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  (∑ x,∑ y,pairBoltzmannWeight α γ J x y*F x y)/(∑ x,∑ y,pairBoltzmannWeight α γ J x y)

lemma pairBoltzmannWeight_factor (α γ J : ℝ) (x y : Bool) :
    pairBoltzmannWeight α γ J x y=cosh α*cosh γ*cosh J*
      ((1+tanh α*spinValue x)*(1+tanh γ*spinValue y)*(1+tanh J*spinValue x*spinValue y)) := by
  unfold pairBoltzmannWeight
  rw [exp_add,exp_add,exp_spin,exp_spin,exp_spin_product]
  ring

lemma pairBoltzmann_partition (α γ J : ℝ) :
    (∑ x,∑ y,pairBoltzmannWeight α γ J x y)=
      4*cosh α*cosh γ*cosh J*(1+tanh J*tanh α*tanh γ) := by
  simp only [pairBoltzmannWeight_factor,Fintype.sum_bool,spinValue_false,spinValue_true]
  ring

lemma pairBoltzmannMean_eq (α γ J : ℝ) (F : Bool→Bool→ℝ) :
    pairBoltzmannMean α γ J F=pairInterMean (tanh α) (tanh γ) (tanh J) F := by
  unfold pairBoltzmannMean pairInterMean pairMean
  rw [pairBoltzmann_partition]
  simp_rw [pairBoltzmannWeight_factor]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  unfold pairBaseMass pairDensity
  have h₁ := (cosh_pos α).ne'
  have h₂ := (cosh_pos γ).ne'
  have h₃ := (cosh_pos J).ne'
  field_simp [h₁,h₂,h₃]

lemma pair_gradients_representation (F : Bool→Bool→ℝ) (a b : ℝ) :
    ∃ p s r : ℝ,
      (∀ y,(F true y-F false y)/2=pairGrad₁ b p r y) ∧
      (∀ x,(F x true-F x false)/2=pairGrad₂ a s r x) := by
  let r := (F true true-F true false-F false true+F false false)/4
  let p := (F true true+F true false-F false true-F false false)/4+b*r
  let s := (F true true-F true false+F false true-F false false)/4+a*r
  refine ⟨p,s,r,?_,?_⟩
  · intro y;cases y <;> simp only [pairGrad₁,spinValue_false,spinValue_true] <;> dsimp [p,r] <;> ring
  · intro x;cases x <;> simp only [pairGrad₂,spinValue_false,spinValue_true] <;> dsimp [s,r] <;> ring

lemma tanh_add_real (a b : ℝ) : tanh (a+b)=(tanh a+tanh b)/(1+tanh a*tanh b) := by
  have h₁ := (cosh_pos a).ne'
  have h₂ := (cosh_pos b).ne'
  have h₃ : cosh a*cosh b+sinh a*sinh b ≠ 0 := by
    rw [← cosh_add]
    exact (cosh_pos (a+b)).ne'
  simp only [tanh_eq_sinh_div_cosh,sinh_add,cosh_add]
  field_simp [h₁,h₂,h₃]

lemma tanh_pair_residual (α J : ℝ) (x y : Bool) :
    spinValue x-tanh (α+J*spinValue y)=pairResidual (tanh α) (tanh J) x y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairResidual
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1; ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases x <;> simp only [spinValue_false,spinValue_true] <;> ring

lemma tanh_pair_variance (α J : ℝ) (y : Bool) :
    1-tanh (α+J*spinValue y)^2=pairVariance (tanh α) (tanh J) y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  unfold pairVariance
  have hd : 1+tanh α*(tanh J*spinValue y) ≠ 0 := by
    have ht : |tanh α*(tanh J*spinValue y)| < 1 := by
      rw [abs_mul,abs_mul,pairSign_abs,mul_one]
      exact (mul_le_mul_of_nonneg_left (abs_tanh_lt_one J).le (abs_nonneg (tanh α))).trans_lt (by simpa using abs_tanh_lt_one α)
    linarith only [(abs_lt.mp ht).1]
  have hd' : 1+tanh J*tanh α*spinValue y ≠ 0 := by
    convert hd using 1; ring
  simp only [← mul_assoc] at hd hd' ⊢
  field_simp [hd,hd']
  cases y <;> simp only [spinValue_false,spinValue_true] <;> ring

end SKRatio.Fields
end
end

end OAI
