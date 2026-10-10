import OAI.NumberTheory.JointDickman.Amplification.FiniteConditionalProduct

namespace OAI

/-! # Uniform conditional residues, including null observation fibers -/

namespace JointDickman
open Finset Classical

theorem uniformImageMass_eq_push {Ω α : Type*} [Fintype Ω] [Fintype α]
    (f : Ω → α) (y : α) :
    uniformImageMass f y = finitePushMass (fun _ : Ω => 1/(Fintype.card Ω : ℝ)) f y := by
  unfold uniformImageMass finitePushMass uniformFiber
  simp only [← sum_filter, sum_const, nsmul_eq_mul]
  ring

theorem uniformConditionalMass_sum {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (hy : 0 < (uniformFiber f y).card) :
    (∑ x, uniformConditionalMass f y x) = 1 := by
  unfold uniformConditionalMass
  rw [← sum_filter]
  change (∑ _x ∈ uniformFiber f y, 1/((uniformFiber f y).card : ℝ)) = 1
  simp only [sum_const,nsmul_eq_mul]
  have h : ((uniformFiber f y).card : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
  field_simp

/-- Null fibers are assigned a point mass. Their observation mass is zero,
so this makes a probability kernel without changing any joint law. -/
noncomputable def totalUniformConditionalMass {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) : ℝ :=
  if (uniformFiber f y).card = 0 then (if x = default then 1 else 0)
  else uniformConditionalMass f y x

theorem totalUniformConditionalMass_nonneg {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) : 0 ≤ totalUniformConditionalMass f y x := by
  unfold totalUniformConditionalMass uniformConditionalMass
  split_ifs <;> positivity

theorem totalUniformConditionalMass_sum {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) : (∑ x, totalUniformConditionalMass f y x) = 1 := by
  by_cases h : (uniformFiber f y).card = 0
  · simp [totalUniformConditionalMass,h]
  · simp only [totalUniformConditionalMass,h,ite_false]
    exact uniformConditionalMass_sum f y (Nat.pos_of_ne_zero h)

theorem total_uniform_image_conditional {Ω α : Type*} [Fintype Ω] [Inhabited Ω]
    (f : Ω → α) (y : α) (x : Ω) :
    uniformImageMass f y * totalUniformConditionalMass f y x =
      if f x = y then 1/(Fintype.card Ω : ℝ) else 0 := by
  by_cases h : (uniformFiber f y).card = 0
  · have hn : f x ≠ y := by
      intro hx
      have hm : x ∈ uniformFiber f y := by simp [uniformFiber,hx]
      have hc := card_pos.mpr ⟨x,hm⟩
      omega
    simp [uniformImageMass,totalUniformConditionalMass,h,hn]
  · simp only [totalUniformConditionalMass,h,ite_false]
    exact uniform_image_conditional f y x

theorem total_uniform_product_disintegration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)] [∀ i, Inhabited (Ω i)]
    (f : ∀ i, Ω i → α i) (F : (∀ i, α i) → (∀ i, Ω i) → ℝ) :
    (∑ x, finiteProductMass (fun i (_ : Ω i) => 1/(Fintype.card (Ω i) : ℝ)) x *
      F (fun i => f i (x i)) x) =
    ∑ y, finiteProductMass (fun i => uniformImageMass (f i)) y *
      ∑ x, finiteProductMass (fun i => totalUniformConditionalMass (f i) (y i)) x * F y x :=
  finiteProduct_disintegration f _ _ _ (fun i y x => total_uniform_image_conditional (f i) y x) F

end JointDickman

end OAI
