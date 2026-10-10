import Mathlib
import OAI.Probability.SKGap.Terminal.PairBoltzmann

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped BigOperators
variable {n : ℕ}

def pairUpdate (i j : Fin n) (x : Spin n) (a b : Bool) : Spin n :=
  Function.update (Function.update x i a) j b

lemma pairUpdate_overwrite (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b c d : Bool) :
    pairUpdate i j (pairUpdate i j x a b) c d=pairUpdate i j x c d := by
  funext k
  by_cases hj : k=j
  · subst k;simp [pairUpdate]
  · by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · simp [pairUpdate,hj,hi]

lemma pairUpdate_left (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b i=a := by simp [pairUpdate,hij]
lemma pairUpdate_right (i j : Fin n) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b j=b := by simp [pairUpdate]

lemma sum_spin_update (i : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ b : Bool,F (Function.update x i b))=2*∑ x,F x := by
  have he (x : Spin n) : (∑ b : Bool,F (Function.update x i b))=F x+F (flip i x) := by
    simp only [Fintype.sum_bool]
    rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_flip]
  ring

lemma sum_pairUpdate (i j : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ a : Bool,∑ b : Bool,F (pairUpdate i j x a b))=4*∑ x,F x := by
  unfold pairUpdate
  rw [sum_spin_update i (fun x=>∑ b : Bool,F (Function.update x j b)),sum_spin_update]
  ring

def pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (F : Spin n→ℝ) (x : Spin n) : ℝ :=
  (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b)*F (pairUpdate i j x a b))/
    (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b))

lemma pairConditionalMean_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) (a b : Bool) :
    pairConditionalMean g h i j F (pairUpdate i j x a b)=pairConditionalMean g h i j F x := by
  simp only [pairConditionalMean,pairUpdate_overwrite i j hij]

lemma pairConditional_partition_pos (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) :
    0 < ∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b) := by
  simp only [Fintype.sum_bool]
  exact add_pos (add_pos (weight_pos _ _ _) (weight_pos _ _ _))
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _))

lemma expectation_pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) : expectation g h (pairConditionalMean g h i j F)=expectation g h F := by
  have h₁ := sum_pairUpdate i j (fun x=>mass g h x*pairConditionalMean g h i j F x)
  have h₂ := sum_pairUpdate i j (fun x=>mass g h x*F x)
  have he : (∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*
      pairConditionalMean g h i j F (pairUpdate i j x a b))=
      ∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*F (pairUpdate i j x a b) := by
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [pairConditionalMean_update g h i j hij,mass,div_mul_eq_mul_div]
    simp only [← Finset.sum_div,← Finset.sum_mul]
    unfold pairConditionalMean
    rw [mul_div_cancel₀ _ (pairConditional_partition_pos g h i j x).ne']
  unfold expectation
  linarith only [h₁,h₂,he]

lemma pairUpdate_hamiltonian (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (x : Spin n) (a b : Bool) :
    let α := localField g h i x-coupling g i j*spinValue (x j);
    let γ := localField g h j x-coupling g i j*spinValue (x i);
    hamiltonian g h (pairUpdate i j x a b)=
      (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
        coupling g i j*spinValue (x i)*spinValue (x j))+
      (α*spinValue a+γ*spinValue b+coupling g i j*spinValue a*spinValue b) := by
  dsimp only
  unfold pairUpdate
  rw [hamiltonian_update,hamiltonian_update,localField_update,
    Function.update_of_ne (Ne.symm hij),coupling_symm g j i]
  ring

lemma pairUpdate_localField₁ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h i (pairUpdate i j x a b)=
      (localField g h i x-coupling g i j*spinValue (x j))+coupling g i j*spinValue b := by
  unfold pairUpdate
  rw [localField_update,localField_update_self]
  by_cases hij : i=j
  · subst j;simp
  · rw [Function.update_of_ne (Ne.symm hij)]
    ring

lemma pairUpdate_localField₂ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h j (pairUpdate i j x a b)=
      (localField g h j x-coupling g i j*spinValue (x i))+coupling g i j*spinValue a := by
  unfold pairUpdate
  rw [localField_update_self,localField_update,coupling_symm g j i]
  ring

lemma pairUpdate_gradient₁ (i j : Fin n) (hij : i ≠ j) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient i F (pairUpdate i j x a b)=
      (F (pairUpdate i j x true b)-F (pairUpdate i j x false b))/2 := by
  have he (c : Bool) : Function.update (pairUpdate i j x a b) i c=pairUpdate i j x c b := by
    funext k
    by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · by_cases hj : k=j
      · subst k;simp [pairUpdate,hij.symm]
      · simp [pairUpdate,hj,hi]
  simp only [spinGradient,he]
lemma pairUpdate_gradient₂ (i j : Fin n) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient j F (pairUpdate i j x a b)=
      (F (pairUpdate i j x a true)-F (pairUpdate i j x a false))/2 := by
  simp only [spinGradient,pairUpdate,Function.update_idem]

lemma pairConditionalMean_boltzmann (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) :
    pairConditionalMean g h i j F x=
      pairBoltzmannMean (localField g h i x-coupling g i j*spinValue (x j))
        (localField g h j x-coupling g i j*spinValue (x i)) (coupling g i j)
        (fun a b=>F (pairUpdate i j x a b)) := by
  let α := localField g h i x-coupling g i j*spinValue (x j)
  let γ := localField g h j x-coupling g i j*spinValue (x i)
  let C := exp (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
    coupling g i j*spinValue (x i)*spinValue (x j))
  have hC : C ≠ 0 := (exp_pos _).ne'
  have hw (a b : Bool) : weight g h (pairUpdate i j x a b)=C*pairBoltzmannWeight α γ (coupling g i j) a b := by
    unfold weight
    rw [pairUpdate_hamiltonian g h i j hij,exp_add]
    rfl
  unfold pairConditionalMean
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hC]
  rfl
end SKGap

end
end

end OAI
