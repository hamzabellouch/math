import OAI.Analysis.KadisonKastler.StateUnitaryCentralizer

namespace OAI

/-! # Algebraic estimates for state centralizer sequences

The state commutator is linear, respects adjoints in norm, and satisfies
an explicit product estimate. These facts support the passage from
unitary tests to all bounded sequences.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

@[simp] theorem vectorStateCommutator_apply (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ a b=vectorFunctional ξ (a*b-b*a) := rfl

@[simp] theorem vectorStateCommutator_add (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (a+b)=vectorStateCommutator ξ a+vectorStateCommutator ξ b := by
  ext c
  simp only [vectorStateCommutator_apply,add_apply,add_mul,mul_add,
    map_sub,map_add]
  ring

@[simp] theorem vectorStateCommutator_smul (ξ : H) (c : ℂ) (a : Algebra M) :
    vectorStateCommutator ξ (c • a)=c • vectorStateCommutator ξ a := by
  ext b
  simp only [vectorStateCommutator_apply,smul_apply,smul_mul_assoc,mul_smul_comm,
    ← smul_sub,map_smul,smul_eq_mul]

@[simp] theorem vectorStateCommutator_zero (ξ : H) :
    vectorStateCommutator (M := M) ξ 0=0 := by
  ext a
  simp only [vectorStateCommutator_apply,zero_mul,mul_zero,sub_self,map_zero,zero_apply]

@[simp] theorem vectorStateCommutator_one (ξ : H) :
    vectorStateCommutator (M := M) ξ 1=0 := by
  ext a
  simp only [vectorStateCommutator_apply,one_mul,mul_one,sub_self,map_zero,zero_apply]

@[simp] theorem vectorStateCommutator_sub (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (a-b)=vectorStateCommutator ξ a-vectorStateCommutator ξ b := by
  ext c
  simp only [vectorStateCommutator_apply,sub_apply,sub_mul,mul_sub,map_sub]
  ring

theorem vectorFunctional_star (ξ : H) (a : Algebra M) :
    vectorFunctional ξ (star a)=star (vectorFunctional ξ a) := by
  change inner ℂ ξ (a.val.adjoint ξ)=star (inner ℂ ξ (a.val ξ))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm (𝕜 := ℂ) (a.val ξ) ξ).symm

theorem vectorStateCommutator_star_apply (ξ : H) (a b : Algebra M) :
    vectorStateCommutator ξ (star a) b = -star (vectorStateCommutator ξ a (star b)) := by
  rw [vectorStateCommutator_apply,vectorStateCommutator_apply,← vectorFunctional_star]
  simp only [star_sub,star_mul,star_star,map_sub]
  abel

theorem vectorStateCommutator_star_norm (ξ : H) (a : Algebra M) :
    ‖vectorStateCommutator ξ (star a)‖=‖vectorStateCommutator ξ a‖ := by
  have h (a : Algebra M) : ‖vectorStateCommutator ξ (star a)‖ ≤
      ‖vectorStateCommutator ξ a‖ := by
    apply (vectorStateCommutator ξ (star a)).opNorm_le_bound (norm_nonneg _)
    intro b
    rw [vectorStateCommutator_star_apply,norm_neg,norm_star]
    simpa only [norm_star] using (vectorStateCommutator ξ a).le_opNorm (star b)
  exact le_antisymm (h a) (by simpa only [star_star] using h (star a))

theorem vectorStateCommutator_mul_apply (ξ : H) (a b x : Algebra M) :
    vectorStateCommutator ξ (a*b) x =
      vectorStateCommutator ξ a (b*x)+vectorStateCommutator ξ b (x*a) := by
  simp only [vectorStateCommutator_apply,map_sub,mul_assoc]
  ring

theorem vectorStateCommutator_mul_norm_le (ξ : H) (a b : Algebra M) :
    ‖vectorStateCommutator ξ (a*b)‖ ≤
      ‖vectorStateCommutator ξ a‖*‖b‖+‖a‖*‖vectorStateCommutator ξ b‖ := by
  apply (vectorStateCommutator ξ (a*b)).opNorm_le_bound (by positivity)
  intro x
  rw [vectorStateCommutator_mul_apply]
  calc
    _ ≤ ‖vectorStateCommutator ξ a (b*x)‖+‖vectorStateCommutator ξ b (x*a)‖ := norm_add_le _ _
    _ ≤ ‖vectorStateCommutator ξ a‖*‖b*x‖+‖vectorStateCommutator ξ b‖*‖x*a‖ :=
      add_le_add ((vectorStateCommutator ξ a).le_opNorm _) ((vectorStateCommutator ξ b).le_opNorm _)
    _ ≤ ‖vectorStateCommutator ξ a‖*(‖b‖*‖x‖)+‖vectorStateCommutator ξ b‖*(‖x‖*‖a‖) := by
      gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

theorem vectorStateCommutator_operator_norm_le (ξ : H) (a : Algebra M) :
    ‖vectorStateCommutator ξ a‖ ≤ 2*‖vectorFunctional (M := M) ξ‖*‖a‖ := by
  apply (vectorStateCommutator ξ a).opNorm_le_bound (by positivity)
  intro b
  rw [vectorStateCommutator_apply]
  calc
    _ ≤ ‖vectorFunctional (M := M) ξ‖*‖a*b-b*a‖ := (vectorFunctional ξ).le_opNorm _
    _ ≤ ‖vectorFunctional (M := M) ξ‖*(‖a*b‖+‖b*a‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
    _ ≤ ‖vectorFunctional (M := M) ξ‖*(‖a‖*‖b‖+‖b‖*‖a‖) := by
      gcongr <;> exact norm_mul_le _ _
    _ = _ := by ring

end

end KadisonKastler

end OAI
