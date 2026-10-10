import OAI.NumberTheory.JointDickman.Amplification.FinitePointMass

namespace OAI

/-! # Exact finite disintegration for coordinate observations -/

namespace JointDickman
open Finset Classical

noncomputable def uniformFiber {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) : Finset Ω := univ.filter (fun x => f x = y)

noncomputable def uniformImageMass {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) : ℝ := (uniformFiber f y).card/(Fintype.card Ω : ℝ)

noncomputable def uniformConditionalMass {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (x : Ω) : ℝ :=
  if f x = y then 1/((uniformFiber f y).card : ℝ) else 0

theorem uniform_image_conditional {Ω α : Type*} [Fintype Ω]
    (f : Ω → α) (y : α) (x : Ω) :
    uniformImageMass f y * uniformConditionalMass f y x =
      if f x = y then 1/(Fintype.card Ω : ℝ) else 0 := by
  by_cases h : f x = y
  · have hc : (uniformFiber f y).card ≠ 0 := by
      apply card_ne_zero.mpr
      exact ⟨x,by simp [uniformFiber,h]⟩
    simp only [uniformImageMass,uniformConditionalMass,h,ite_true]
    have hc' : ((uniformFiber f y).card : ℝ) ≠ 0 := by exact_mod_cast hc
    field_simp
  · simp [uniformConditionalMass,h]

/-- Observation kernels can be multiplied before disintegrating, even when
the final test depends on the whole observed family. -/
theorem finiteProduct_disintegration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)]
    (f : ∀ i, Ω i → α i) (w : ∀ i, Ω i → ℝ)
    (a : ∀ i, α i → ℝ) (k : ∀ i, α i → Ω i → ℝ)
    (hk : ∀ i y x, a i y*k i y x = if f i x = y then w i x else 0)
    (F : (∀ i, α i) → (∀ i, Ω i) → ℝ) :
    (∑ x, finiteProductMass w x * F (fun i => f i (x i)) x) =
      ∑ y, finiteProductMass a y *
        ∑ x, finiteProductMass (fun i => k i (y i)) x * F y x := by
  have hprod (x : ∀ i, Ω i) (y : ∀ i, α i) :
      finiteProductMass a y * finiteProductMass (fun i => k i (y i)) x =
        if (fun i => f i (x i)) = y then finiteProductMass w x else 0 := by
    simp only [finiteProductMass,← prod_mul_distrib,hk]
    by_cases he : (fun i => f i (x i)) = y
    · have he' (i : ι) : f i (x i) = y i := congrFun he i
      simp [he']
    · rw [ite_eq_right he]
      obtain ⟨i,hi⟩ : ∃ i, f i (x i) ≠ y i := by
        by_contra h
        push Not at h
        exact he (funext h)
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  symm
  simp only [mul_sum,← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp only [hprod,ite_mul,zero_mul]
  simp

theorem uniformProduct_disintegration {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω α : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (α i)]
    (f : ∀ i, Ω i → α i) (F : (∀ i, α i) → (∀ i, Ω i) → ℝ) :
    (∑ x, finiteProductMass (fun i (_ : Ω i) => 1/(Fintype.card (Ω i) : ℝ)) x *
      F (fun i => f i (x i)) x) =
    ∑ y, finiteProductMass (fun i => uniformImageMass (f i)) y *
      ∑ x, finiteProductMass (fun i => uniformConditionalMass (f i) (y i)) x * F y x :=
  finiteProduct_disintegration f _ _ _ (fun i y x => uniform_image_conditional (f i) y x) F

end JointDickman

end OAI
