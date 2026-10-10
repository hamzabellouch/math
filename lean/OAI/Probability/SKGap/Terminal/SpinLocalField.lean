import Mathlib
import OAI.Probability.SKGap.Terminal.FiniteSpinCalculus

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators
variable {n : ℕ}

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
end SKGap

end
end

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators

def pairBaseMass (a b : ℝ) (x y : Bool) : ℝ :=
  (1+a*spinValue x)*(1+b*spinValue y)/4

def pairMean (a b : ℝ) (F : Bool→Bool→ℝ) : ℝ :=
  ∑ x,∑ y,pairBaseMass a b x y*F x y

lemma pairMean_explicit (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=((1-a)*(1-b)*F false false+(1-a)*(1+b)*F false true+
      (1+a)*(1-b)*F true false+(1+a)*(1+b)*F true true)/4 := by
  simp only [pairMean,Fintype.sum_bool,pairBaseMass,spinValue,Bool.false_eq_true,
    ite_false,ite_true,mul_neg_one,mul_one]
  ring

lemma pairBaseMass_nonneg {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (x y : Bool) :
    0 ≤ pairBaseMass a b x y := by
  have h₁ := abs_le.mp ha
  have h₂ := abs_le.mp hb
  unfold pairBaseMass
  cases x <;> cases y <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,mul_one,mul_neg_one] <;>
    exact div_nonneg (mul_nonneg (by linarith only [h₁.1,h₁.2]) (by linarith only [h₂.1,h₂.2])) (by norm_num)

lemma pairMean_mono {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    {F G : Bool→Bool→ℝ} (h : ∀ x y,F x y ≤ G x y) : pairMean a b F ≤ pairMean a b G := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (h x y) (pairBaseMass_nonneg ha hb x y)

lemma pairMean_add (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y+G x y)=pairMean a b F+pairMean a b G := by
  simp only [pairMean,mul_add,Finset.sum_add_distrib]
lemma pairMean_sub (a b : ℝ) (F G : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>F x y-G x y)=pairMean a b F-pairMean a b G := by
  simp only [pairMean,mul_sub,Finset.sum_sub_distrib]
lemma pairMean_mul (a b c : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b (fun x y=>c*F x y)=c*pairMean a b F := by
  simp only [pairMean,Finset.mul_sum,mul_left_comm]

lemma abs_pairMean_le {a b : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (F : Bool→Bool→ℝ) : |pairMean a b F| ≤ pairMean a b (fun x y=>|F x y|) := by
  unfold pairMean
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
  apply Finset.sum_congr rfl
  intro y _
  rw [abs_mul,abs_of_nonneg (pairBaseMass_nonneg ha hb x y)]

lemma pair_gradient_mean (a b p s r : ℝ) :
    pairMean a b (fun x y=>(p+r*(spinValue y-b))*(s+r*(spinValue x-a)))=p*s := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pair_gradient_square (a b p r : ℝ) :
    pairMean a b (fun _ y=>(p+r*(spinValue y-b))^2)=p^2+(1-b^2)*r^2 := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring

lemma pairMean_swap (a b : ℝ) (F : Bool→Bool→ℝ) :
    pairMean a b F=pairMean b a (fun x y=>F y x) := by
  rw [pairMean_explicit,pairMean_explicit]
  ring

lemma pair_second_gradient_square (a b s r : ℝ) :
    pairMean a b (fun x _=>(s+r*(spinValue x-a))^2)=s^2+(1-a^2)*r^2 := by
  rw [pairMean_swap]
  exact pair_gradient_square b a s r

lemma pair_polynomial_cross_mean (a b u c₁ d₁ c₂ d₂ : ℝ) :
    pairMean a b (fun x y=>(spinValue x-a)*(spinValue y-b)*(1-u*spinValue x*spinValue y)*
      (c₁+spinValue y*d₁)*(c₂+spinValue x*d₂))=
      (1-a^2)*(1-b^2)*(d₁*d₂-u*c₁*c₂) := by
  rw [pairMean_explicit]
  simp only [spinValue,Bool.false_eq_true,ite_false,ite_true]
  ring
end SKGap

end
end

end OAI
