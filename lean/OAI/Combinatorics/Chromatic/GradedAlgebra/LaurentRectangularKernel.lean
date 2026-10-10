import Mathlib

namespace OAI

section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

noncomputable def rectangular {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) : G :=
  ∏ i,∏ j,∏ x : L i,∏ y : R j,v i j x y ^ b i j

lemma rectangular_add {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b c : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (b+c) v=rectangular b v*rectangular c v := by
  simp only [rectangular,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]

lemma rectangular_neg {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (-b) v=(rectangular b v)⁻¹ := by
  simp only [rectangular,Pi.neg_apply,zpow_neg,Finset.prod_inv_distrib]

lemma rectangular_sub {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b c : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (b-c) v=rectangular b v*(rectangular c v)⁻¹ := by
  rw [sub_eq_add_neg,rectangular_add,rectangular_neg]

lemma rectangular_map {H : Type*} [CommGroup H] (f : G →* H)
    {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    f (rectangular b v)=rectangular b (fun i j x y=>f (v i j x y)) := by
  simp only [rectangular,map_prod,map_zpow]

lemma rectangular_transpose {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v : ∀ i j,L i → R j → G) :
    rectangular (fun i j=>b j i) (fun i j (x:R i) (y:L j)=>v j i y x)=
      rectangular b v := by
  unfold rectangular
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  exact Finset.prod_comm

lemma rectangular_sum {L₁ L₂ R₁ R₂ : I → Type*}
    [∀ i,Fintype (L₁ i)] [∀ i,Fintype (L₂ i)]
    [∀ i,Fintype (R₁ i)] [∀ i,Fintype (R₂ i)]
    (b : I → I → ℤ) (v : ∀ i j,(L₁ i⊕L₂ i) → (R₁ j⊕R₂ j) → G) :
    rectangular b v=
      rectangular b (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
      rectangular b (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))*
      rectangular b (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))*
      rectangular b (fun i j x y=>v i j (Sum.inr x) (Sum.inr y)) := by
  simp only [rectangular,Fintype.prod_sum_type,Finset.prod_mul_distrib]
  ac_rfl

lemma rectangular_diagonal [DecidableEq I] {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (v : ∀ i j,L i → R j → G) :
    rectangular (fun i j=>if i=j then 1 else 0) v=
      ∏ i,∏ x:L i,∏ y:R i,v i i x y := by
  unfold rectangular
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [Ne.symm hji]
  · simp

lemma four_rectangle_cancellation {L₁ L₂ R₁ R₂ : I → Type*}
    [∀ i,Fintype (L₁ i)] [∀ i,Fintype (L₂ i)]
    [∀ i,Fintype (R₁ i)] [∀ i,Fintype (R₂ i)]
    (δ a : I → I → ℤ) (v : ∀ i j,(L₁ i⊕L₂ i) → (R₁ j⊕R₂ j) → G) :
    rectangular (δ-a) v * (rectangular δ v)⁻¹ *
      (rectangular δ (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
       rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))*
       rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))*
       rectangular (fun i j=>a j i) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))) =
    rectangular (δ-a) (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))*
    rectangular (δ-a) (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))*
      (rectangular (δ-a) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))*
       (rectangular (δ-(fun i j=>a j i)) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y)))⁻¹) := by
  rw [rectangular_sub δ a v,rectangular_sum a v]
  rw [rectangular_sub,rectangular_sub,rectangular_sub,rectangular_sub]
  generalize rectangular δ v=K
  generalize rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))=A
  generalize rectangular a (fun i j x y=>v i j (Sum.inl x) (Sum.inr y))=B
  generalize rectangular a (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=C
  generalize rectangular a (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))=D
  generalize rectangular δ (fun i j x y=>v i j (Sum.inl x) (Sum.inl y))=P
  generalize rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inr y))=Q
  generalize rectangular δ (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=R
  generalize rectangular (fun i j=>a j i) (fun i j x y=>v i j (Sum.inr x) (Sum.inl y))=S
  simp [mul_comm,mul_left_comm,mul_assoc]
  rw [mul_left_comm B P,mul_left_comm B Q,mul_left_comm B S,mul_left_comm B A⁻¹,
    mul_inv_cancel_left]

end ElementaryPositivity.RectangularKernel

end
section
namespace ElementaryPositivity.RectangularKernel
variable {I : Type*} [Fintype I]
variable {G : Type*} [CommGroup G]

lemma rectangular_mul {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (v w : ∀ i j,L i → R j → G) :
    rectangular b (fun i j x y=>v i j x y*w i j x y)=rectangular b v*rectangular b w := by
  simp only [rectangular,mul_zpow,Finset.prod_mul_distrib]

lemma prod_zpow_sum {α : Type*} (s : Finset α) (b : α → ℤ) (g : G) :
    (∏ x∈s,g^b x)=g^(∑ x∈s,b x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih => rw [Finset.prod_insert hx,Finset.sum_insert hx,ih,zpow_add]

lemma rectangular_constant {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (g : G) :
    rectangular (L:=L) (R:=R) b (fun _ _ _ _=>g)=
      g^(∑ i,∑ j,b i j*(Fintype.card (L i):ℤ)*(Fintype.card (R j):ℤ)) := by
  simp only [rectangular,Finset.prod_const,Finset.card_univ,←zpow_natCast,←zpow_mul]
  rw [←prod_zpow_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [←prod_zpow_sum]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  ring

lemma rectangular_scalar_mul {L R : I → Type*} [∀ i,Fintype (L i)] [∀ i,Fintype (R i)]
    (b : I → I → ℤ) (g : G) (v : ∀ i j,L i → R j → G) :
    rectangular b (fun i j x y=>g*v i j x y)=
      g^(∑ i,∑ j,b i j*(Fintype.card (L i):ℤ)*(Fintype.card (R j):ℤ))*rectangular b v := by
  rw [rectangular_mul,rectangular_constant]

end ElementaryPositivity.RectangularKernel

end

end OAI
