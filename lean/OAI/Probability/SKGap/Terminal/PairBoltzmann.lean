import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalMatrixTransfer
import OAI.Probability.SKGap.Terminal.PairCrossLower

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

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

lemma pairBoltzmann_signed_bound (α γ J : ℝ) (F : Bool→Bool→ℝ)
    (hJ : |tanh J| ≤ 1/1000) :
    let g₁ := fun y=>(F true y-F false y)/2;
    let g₂ := fun x=>(F x true-F x false)/2;
    let v₁ := fun y=>1-tanh (α+J*spinValue y)^2;
    let v₂ := fun x=>1-tanh (γ+J*spinValue x)^2;
    -tanh J*pairBoltzmannMean α γ J (fun x y=>v₁ y*g₁ y*(v₂ x*g₂ x))-
      400000*(tanh J)^2*pairBoltzmannMean α γ J (fun x y=>|v₁ y*g₁ y*(v₂ x*g₂ x)|)-
      400000*(tanh J)^4*pairBoltzmannMean α γ J (fun x y=>v₁ y*(g₁ y)^2+v₂ x*(g₂ x)^2) ≤
    pairBoltzmannMean α γ J (fun x y=>(spinValue x-tanh (α+J*spinValue y))*g₁ y*
      ((spinValue y-tanh (γ+J*spinValue x))*g₂ x)) := by
  dsimp only
  obtain ⟨p,s,r,hg₁,hg₂⟩ := pair_gradients_representation F (tanh α) (tanh γ)
  simp_rw [pairBoltzmannMean_eq,tanh_pair_residual,tanh_pair_variance,hg₁,hg₂]
  exact pair_signed_bound (abs_tanh_lt_one α).le (abs_tanh_lt_one γ).le hJ
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

lemma update_true_false (i : Fin n) (x : Spin n) :
    (Function.update x i true=x ∧ Function.update x i false=flip i x) ∨
      (Function.update x i true=flip i x ∧ Function.update x i false=x) := by
  cases hx : x i
  · right
    constructor
    · simp [flip,hx]
    · simpa only [hx] using Function.update_eq_self i x
  · left
    constructor
    · simpa only [hx] using Function.update_eq_self i x
    · simp [flip,hx]

lemma conditionalExpectation_updates (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (∑ b : Bool,weight g h (Function.update x i b)*f (Function.update x i b))/
      (∑ b : Bool,weight g h (Function.update x i b)) := by
  simp only [Fintype.sum_bool]
  rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]
  · rfl
  · unfold conditionalExpectation
    rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma weight_update_factor (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    weight g h (Function.update x i b)=exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
      exp (localField g h i x*spinValue b) := by
  unfold weight
  rw [hamiltonian_update,← exp_add]
  congr 1;ring

lemma conditionalExpectation_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (f (Function.update x i true)+f (Function.update x i false))/2+
        tanh (localField g h i x)*spinGradient i f x := by
  rw [conditionalExpectation_updates]
  simp_rw [weight_update_factor,exp_spin]
  simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  unfold spinGradient
  have h₁ := (exp_pos (hamiltonian g h x-spinValue (x i)*localField g h i x)).ne'
  have h₂ := (cosh_pos (localField g h i x)).ne'
  have he : exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+tanh (localField g h i x)))+
      exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+-tanh (localField g h i x)))=
      2*exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*cosh (localField g h i x) := by ring
  rw [he]
  field_simp [h₁,h₂]
  ring

lemma spin_affine (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    f x=(f (Function.update x i true)+f (Function.update x i false))/2+
      spinValue (x i)*spinGradient i f x := by
  unfold spinGradient
  cases hx : x i
  · have hf : Function.update x i false=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_false,hf];ring
  · have ht : Function.update x i true=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_true,ht];ring

lemma conditionalDifference_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    f x-conditionalExpectation g h i f x=
      (spinValue (x i)-tanh (localField g h i x))*spinGradient i f x := by
  rw [conditionalExpectation_local]
  have he := spin_affine i f x
  linarith only [he]

lemma spinGradient_update (i : Fin n) (f : Spin n→ℝ) (x : Spin n) (b : Bool) :
    spinGradient i f (Function.update x i b)=spinGradient i f x := by
  simp only [spinGradient,Function.update_idem]

lemma conditionalSiteEnergy_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>(1-tanh (localField g h i x)^2)*spinGradient i f x^2) := by
  rw [← expectation_conditionalExpectation g h i]
  congr 1
  funext x
  rw [conditionalExpectation_local]
  simp_rw [conditionalDifference_local,localField_update_self,spinGradient_update]
  simp only [Function.update_self,spinValue_true,spinValue_false,spinGradient]
  simp_rw [Function.update_idem,localField_update_self]
  ring
end SKGap

end
end

end OAI
