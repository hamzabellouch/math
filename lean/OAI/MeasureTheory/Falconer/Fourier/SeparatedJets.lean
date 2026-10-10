import OAI.MeasureTheory.Falconer.Estimates.LaplacianBounds

namespace OAI

/-! # Finite separated symbols and their actual derivatives

The two external parameters remain in different factors. Directional
derivatives use the ordinary product rule, so taking finitely many chart
jets never introduces a joint endpoint symbol.
-/

namespace Falconer
open scoped ContDiff

variable {X Y E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure SmoothSeparation (X Y E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  index : Type
  finite : Fintype index
  left : index → X → E → ℂ
  right : index → Y → E → ℂ
  left_smooth : ∀ i x, ContDiff ℝ ∞ (left i x)
  right_smooth : ∀ i y, ContDiff ℝ ∞ (right i y)

attribute [instance] SmoothSeparation.finite

namespace SmoothSeparation

noncomputable def value (S : SmoothSeparation X Y E) (x : X) (y : Y) (z : E) : ℂ :=
  ∑ i : S.index, S.left i x z*S.right i y z

theorem value_contDiff (S : SmoothSeparation X Y E) (x : X) (y : Y) :
    ContDiff ℝ ∞ (S.value x y) :=
  ContDiff.sum (fun i _ => (S.left_smooth i x).mul (S.right_smooth i y))

noncomputable def product (a : X → E → ℂ) (b : Y → E → ℂ)
    (ha : ∀ x, ContDiff ℝ ∞ (a x)) (hb : ∀ y, ContDiff ℝ ∞ (b y)) :
    SmoothSeparation X Y E where
  index := Unit
  finite := inferInstance
  left := fun _ => a
  right := fun _ => b
  left_smooth := fun _ => ha
  right_smooth := fun _ => hb

@[simp] theorem product_value (a : X → E → ℂ) (b : Y → E → ℂ)
    (ha : ∀ x, ContDiff ℝ ∞ (a x)) (hb : ∀ y, ContDiff ℝ ∞ (b y))
    (x : X) (y : Y) (z : E) : (product a b ha hb).value x y z = a x z*b y z := by
  change (∑ _i : Unit, a x z*b y z) = a x z*b y z
  simp

noncomputable def mulLeft (S : SmoothSeparation X Y E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) : SmoothSeparation X Y E where
  index := S.index
  finite := S.finite
  left := fun i x z => c z*S.left i x z
  right := S.right
  left_smooth := fun i x => hc.mul (S.left_smooth i x)
  right_smooth := S.right_smooth

@[simp] theorem mulLeft_value (S : SmoothSeparation X Y E) (c : E → ℂ)
    (hc : ContDiff ℝ ∞ c) (x : X) (y : Y) (z : E) :
    (S.mulLeft c hc).value x y z = c z*S.value x y z := by
  simp only [value,mulLeft,Finset.mul_sum,mul_assoc]
  rfl

noncomputable def pullback (S : SmoothSeparation X Y E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) : SmoothSeparation X Y H where
  index := S.index
  finite := S.finite
  left := fun i x => S.left i x ∘ g
  right := fun i y => S.right i y ∘ g
  left_smooth := fun i x => (S.left_smooth i x).comp hg
  right_smooth := fun i y => (S.right_smooth i y).comp hg

@[simp] theorem pullback_value (S : SmoothSeparation X Y E) (g : H → E)
    (hg : ContDiff ℝ ∞ g) (x : X) (y : Y) (z : H) :
    (S.pullback g hg).value x y z = S.value x y (g z) := rfl

noncomputable def derivative (S : SmoothSeparation X Y E) (v : E) :
    SmoothSeparation X Y E where
  index := S.index ⊕ S.index
  finite := inferInstance
  left := Sum.elim (fun i x z => fderiv ℝ (S.left i x) z v) S.left
  right := Sum.elim S.right (fun i y z => fderiv ℝ (S.right i y) z v)
  left_smooth := by
    intro i x
    cases i with
    | inl i => exact ((S.left_smooth i x).fderiv_right (by simp)).clm_apply contDiff_const
    | inr i => exact S.left_smooth i x
  right_smooth := by
    intro i y
    cases i with
    | inl i => exact S.right_smooth i y
    | inr i => exact ((S.right_smooth i y).fderiv_right (by simp)).clm_apply contDiff_const

theorem derivative_value (S : SmoothSeparation X Y E) (v : E)
    (x : X) (y : Y) (z : E) :
    (S.derivative v).value x y z = fderiv ℝ (S.value x y) z v := by
  change _ = fderiv ℝ (fun w => ∑ i : S.index, S.left i x w*S.right i y w) z v
  rw [fderiv_fun_sum (A := fun i (w : E) => S.left i x w*S.right i y w)
    (u := Finset.univ) (fun i _ =>
    ((S.left_smooth i x).differentiable (by simp)).differentiableAt.mul
      ((S.right_smooth i y).differentiable (by simp)).differentiableAt)]
  change (∑ i : S.index ⊕ S.index,
    Sum.elim (fun j x z => fderiv ℝ (S.left j x) z v) S.left i x z *
      Sum.elim S.right (fun j y z => fderiv ℝ (S.right j y) z v) i y z) = _
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul
    ((S.left_smooth i x).differentiable (by simp)).differentiableAt
    ((S.right_smooth i y).differentiable (by simp)).differentiableAt]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

noncomputable def sum {I : Type} [Fintype I] (S : I → SmoothSeparation X Y E) :
    SmoothSeparation X Y E where
  index := (i : I) × (S i).index
  finite := inferInstance
  left := fun i => (S i.1).left i.2
  right := fun i => (S i.1).right i.2
  left_smooth := fun i => (S i.1).left_smooth i.2
  right_smooth := fun i => (S i.1).right_smooth i.2

@[simp] theorem sum_value {I : Type} [Fintype I] (S : I → SmoothSeparation X Y E)
    (x : X) (y : Y) (z : E) :
    (sum S).value x y z = ∑ i : I, (S i).value x y z := by
  change (∑ i : (j : I) × (S j).index, (S i.1).left i.2 x z*(S i.1).right i.2 y z) = _
  exact Fintype.sum_sigma _

noncomputable def laplacian {n : ℕ} (S : SmoothSeparation X Y E) (v : Fin n → E) :
    SmoothSeparation X Y E :=
  sum (fun i => (S.derivative (v i)).derivative (v i))

theorem laplacian_value {n : ℕ} (S : SmoothSeparation X Y E) (v : Fin n → E)
    (x : X) (y : Y) (z : E) :
    (S.laplacian v).value x y z = directionalLaplacian v (S.value x y) z := by
  rw [laplacian,sum_value,directionalLaplacian,directionalLaplacianTrace_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_value]
  have he : (S.derivative (v i)).value x y = fun w => fderiv ℝ (S.value x y) w (v i) :=
    funext (S.derivative_value (v i) x y)
  rw [he]
  have hdf : ContDiff ℝ ∞ (fderiv ℝ (S.value x y)) :=
    (S.value_contDiff x y).fderiv_right (by simp)
  have hf : Differentiable ℝ (fderiv ℝ (S.value x y)) := hdf.differentiable (by simp)
  have hc := ((ContinuousLinearMap.apply ℝ ℂ (v i)).hasFDerivAt.comp z
    hf.differentiableAt.hasFDerivAt).fderiv
  have hv := congrArg (fun T : E →L[ℝ] ℂ => T (v i)) hc
  exact hv

noncomputable def iteratedLaplacian {n : ℕ} (S : SmoothSeparation X Y E)
    (v : Fin n → E) (j : ℕ) : SmoothSeparation X Y E :=
  (fun T : SmoothSeparation X Y E => T.laplacian v)^[j] S

theorem iteratedLaplacian_value {n : ℕ} (S : SmoothSeparation X Y E) (v : Fin n → E)
    (j : ℕ) (x : X) (y : Y) :
    (S.iteratedLaplacian v j).value x y = (directionalLaplacian v)^[j] (S.value x y) := by
  induction j with
  | zero => rfl
  | succ j hj =>
    simp only [iteratedLaplacian,Function.iterate_succ_apply']
    funext z
    rw [laplacian_value]
    change directionalLaplacian v ((S.iteratedLaplacian v j).value x y) z = _
    rw [hj]

end SmoothSeparation
end Falconer

end OAI
