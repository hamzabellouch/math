import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.UnitalCoproductUnits

namespace OAI

section
namespace ElementaryPositivity.TensorTransport
open scoped TensorProduct
variable {M N P X : Type*} [AddCommGroup M] [Module ℚ M]
  [AddCommGroup N] [Module ℚ N] [AddCommGroup P] [Module ℚ P]
  [AddCommGroup X] [Module ℚ X]
lemma map_left_insert (f : X →ₗ[ℚ] M⊗[ℚ]N) (g : X →ₗ[ℚ] N)
    (u : M) (hf : ∀ x,f x=u⊗ₜ[ℚ]g x) (x : X⊗[ℚ]P) :
    TensorProduct.assoc ℚ M N P (TensorProduct.map f LinearMap.id x)=
      u⊗ₜ[ℚ]TensorProduct.map g LinearMap.id x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,TensorProduct.tmul_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.assoc_tmul]
lemma map_right_insert (f : X →ₗ[ℚ] N⊗[ℚ]P) (g : X →ₗ[ℚ] N)
    (u : P) (hf : ∀ x,f x=g x⊗ₜ[ℚ]u) (x : M⊗[ℚ]X) :
    TensorProduct.map LinearMap.id f x=
      TensorProduct.assoc ℚ M N P (TensorProduct.map LinearMap.id g x⊗ₜ[ℚ]u) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,TensorProduct.add_tmul,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.assoc_tmul]
lemma map_middle_left (f : X →ₗ[ℚ] M⊗[ℚ]N) (g : X →ₗ[ℚ] M)
    (u : N) (hf : ∀ x,f x=g x⊗ₜ[ℚ]u) (x : X⊗[ℚ]P) :
    TensorProduct.assoc ℚ M N P (TensorProduct.map f LinearMap.id x)=
      TensorProduct.map LinearMap.id (TensorProduct.mk ℚ N P u)
        (TensorProduct.map g LinearMap.id x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,
      TensorProduct.assoc_tmul,TensorProduct.mk_apply]
lemma map_middle_right (f : X →ₗ[ℚ] N⊗[ℚ]P) (g : X →ₗ[ℚ] P)
    (u : N) (hf : ∀ x,f x=u⊗ₜ[ℚ]g x) (x : M⊗[ℚ]X) :
    TensorProduct.map LinearMap.id f x=
      TensorProduct.map LinearMap.id (TensorProduct.mk ℚ N P u)
        (TensorProduct.map LinearMap.id g x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp only [TensorProduct.map_tmul,LinearMap.id_apply,hf,TensorProduct.mk_apply]
end ElementaryPositivity.TensorTransport

namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] unitalSepTensor unitalSepTensorA
noncomputable local instance naturalTensorAdd (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    AddCommGroup (B a μ d⊗[ℚ]B a μ e) := TensorProduct.addCommGroup
noncomputable local instance naturalTensorModule (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d e : I → ℕ) :
    Module ℚ (B a μ d⊗[ℚ]B a μ e) := TensorProduct.leftModule

noncomputable def castBLinear (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) : B a μ d →ₗ[ℚ] B a μ e := by
  subst e
  exact LinearMap.id

lemma castBLinear_apply (a : I → I → ℕ) (μ : (I → ℕ) → ℝ)
    {d e : I → ℕ} (h : d=e) (x : B a μ d) :
    castBLinear a μ h x=castB a μ h x := by subst e; rfl

lemma castBLinear_rfl (a : I → I → ℕ) (μ : (I → ℕ) → ℝ) (d : I → ℕ) :
    castBLinear a μ (rfl : d=d)=LinearMap.id := rfl

lemma unitalSeparationConstant_cast (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) {d e d' e' : I → ℕ} (hd : d=d') (he : e=e')
    (hs : d=0 ∨ e=0 ∨ slope c η d=slope c η e)
    (hs' : d'=0 ∨ e'=0 ∨ slope c η d'=slope c η e')
    (x : B a (slope c η) (d+e)) :
    unitalSeparationConstant a c η hc d' e' hs'
      (castB a (slope c η) (congrArg₂ (·+·) hd he) x)=
    TensorProduct.map (castBLinear a (slope c η) hd) (castBLinear a (slope c η) he)
      (unitalSeparationConstant a c η hc d e hs x) := by
  subst d'; subst e'
  simp only [castB_rfl,castBLinear_rfl,TensorProduct.map_id,LinearMap.id_apply]

lemma unitalSeparationConstant_zero_left_any (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (d : I → ℕ) (x : B a (slope c η) (0+d)) :
    unitalSeparationConstant a c η hc 0 d (Or.inl rfl) x=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]castB a (slope c η) (zero_add d) x := by
  have h := unitalSeparationConstant_zero_left a c η hc d
    (castB a (slope c η) (zero_add d) x)
  simpa only [castB_trans,castB_rfl] using h

lemma unitalSeparationConstant_zero_right_any (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (d : I → ℕ) (x : B a (slope c η) (d+0)) :
    unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl)) x=
      castB a (slope c η) (add_zero d) x⊗ₜ[ℚ](1:B a (slope c η) 0) := by
  have h := unitalSeparationConstant_zero_right a c η hc d
    (castB a (slope c η) (add_zero d) x)
  simpa only [castB_trans,castB_rfl] using h

lemma unitalSeparationConstant_map_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (e f : I → ℕ)
    (x : B a (slope c η) (0+e)⊗[ℚ]B a (slope c η) f) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc 0 e (Or.inl rfl)) LinearMap.id x)=
      (1:B a (slope c η) 0)⊗ₜ[ℚ]
        TensorProduct.map (castBLinear a (slope c η) (zero_add e)) LinearMap.id x := by
  apply TensorTransport.map_left_insert
  intro y
  rw [castBLinear_apply]
  exact unitalSeparationConstant_zero_left_any a c η hc e y

lemma unitalSeparationConstant_map_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (d e : I → ℕ)
    (x : B a (slope c η) d⊗[ℚ]B a (slope c η) (e+0)) :
    TensorProduct.map LinearMap.id (unitalSeparationConstant a c η hc e 0 (Or.inr (Or.inl rfl))) x=
      TensorProduct.assoc ℚ _ _ _
        ((TensorProduct.map LinearMap.id (castBLinear a (slope c η) (add_zero e)) x)⊗ₜ[ℚ]
          (1:B a (slope c η) 0)) := by
  apply TensorTransport.map_right_insert
  intro y
  rw [castBLinear_apply]
  exact unitalSeparationConstant_zero_right_any a c η hc e y

lemma unitalCoproduct_coassoc_zero_left (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (e f : I → ℕ)
    (he : OnSlopeOrZero c η θ e) (hf : OnSlopeOrZero c η θ f)
    (x : B a (slope c η) ((0+e)+f)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc 0 e (Or.inl rfl)) LinearMap.id
        (unitalSeparationConstant a c η hc (0+e) f
          ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc he |>.compatible hf) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e f (he.compatible hf))
        (unitalSeparationConstant a c η hc 0 (e+f) (Or.inl rfl)
          (castB a (slope c η) (add_assoc 0 e f) x)) := by
  rw [unitalSeparationConstant_map_zero_left]
  have h := unitalSeparationConstant_cast a c η hc (zero_add e) (rfl : f=f)
    ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc he |>.compatible hf) (he.compatible hf) x
  simp only [castBLinear_rfl] at h ⊢
  rw [←h]
  rw [unitalSeparationConstant_zero_left_any,TensorProduct.map_tmul,LinearMap.id_apply,
    castB_trans]

lemma unitalCoproduct_coassoc_zero_right (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d e : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (he : OnSlopeOrZero c η θ e)
    (x : B a (slope c η) ((d+e)+0)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d e (hd.compatible he)) LinearMap.id
        (unitalSeparationConstant a c η hc (d+e) 0 (Or.inr (Or.inl rfl)) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc e 0 (Or.inr (Or.inl rfl)))
        (unitalSeparationConstant a c η hc d (e+0)
          (hd.compatible (he.add hc (Or.inl rfl)))
          (castB a (slope c η) (add_assoc d e 0) x)) := by
  rw [unitalSeparationConstant_map_zero_right]
  have h := unitalSeparationConstant_cast a c η hc (rfl : d=d) (add_zero e)
    (hd.compatible (he.add hc (Or.inl rfl))) (hd.compatible he)
    (castB a (slope c η) (add_assoc d e 0) x)
  simp only [castBLinear_rfl] at h ⊢
  rw [←h]
  rw [unitalSeparationConstant_zero_right_any,TensorProduct.map_tmul,LinearMap.id_apply,
    castB_trans]

lemma unitalCoproduct_coassoc_zero_middle (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0<c i) (θ : ℝ) (d f : I → ℕ)
    (hd : OnSlopeOrZero c η θ d) (hf : OnSlopeOrZero c η θ f)
    (x : B a (slope c η) ((d+0)+f)) :
    TensorProduct.assoc ℚ _ _ _
      (TensorProduct.map (unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl))) LinearMap.id
        (unitalSeparationConstant a c η hc (d+0) f
          ((hd.add hc (Or.inl rfl)).compatible hf) x))=
      TensorProduct.map LinearMap.id
        (unitalSeparationConstant a c η hc 0 f (Or.inl rfl))
        (unitalSeparationConstant a c η hc d (0+f)
          (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
          (castB a (slope c η) (add_assoc d 0 f) x)) := by
  have hL := TensorTransport.map_middle_left
    (unitalSeparationConstant a c η hc d 0 (Or.inr (Or.inl rfl)))
    (castBLinear a (slope c η) (add_zero d)) (1:B a (slope c η) 0)
    (fun y=>by rw [castBLinear_apply]; exact unitalSeparationConstant_zero_right_any a c η hc d y)
    (unitalSeparationConstant a c η hc (d+0) f ((hd.add hc (Or.inl rfl)).compatible hf) x)
  have hR := TensorTransport.map_middle_right
    (unitalSeparationConstant a c η hc 0 f (Or.inl rfl))
    (castBLinear a (slope c η) (zero_add f)) (1:B a (slope c η) 0)
    (fun y=>by rw [castBLinear_apply]; exact unitalSeparationConstant_zero_left_any a c η hc f y)
    (unitalSeparationConstant a c η hc d (0+f)
      (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
      (castB a (slope c η) (add_assoc d 0 f) x))
  rw [hL,hR]
  have hL' := unitalSeparationConstant_cast a c η hc (add_zero d) (rfl : f=f)
    ((hd.add hc (Or.inl rfl)).compatible hf) (hd.compatible hf) x
  have hR' := unitalSeparationConstant_cast a c η hc (rfl : d=d) (zero_add f)
    (hd.compatible ((show OnSlopeOrZero c η θ 0 from Or.inl rfl).add hc hf))
    (hd.compatible hf) (castB a (slope c η) (add_assoc d 0 f) x)
  simp only [castBLinear_rfl] at hL' hR' ⊢
  rw [←hL',←hR',castB_trans]

end ElementaryPositivity.RawShuffle

end

end OAI
