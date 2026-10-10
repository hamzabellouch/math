import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
attribute [local instance] Classical.propDecidable

namespace Problem315.FiniteCellProjection

variable {Ω : Type*} [Fintype Ω]

def restrict (p : Ω → Prop) :
    EuclideanSpace ℝ Ω →ₗ[ℝ] EuclideanSpace ℝ {x // p x} where
  toFun f := WithLp.toLp 2 (fun x => f x.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extend (p : Ω → Prop) :
    EuclideanSpace ℝ {x // p x} →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun f := WithLp.toLp 2 (fun x => if h : p x then f ⟨x,h⟩ else 0)
  map_add' f g := by
    ext x
    by_cases h : p x <;> simp [h]
  map_smul' c f := by
    ext x
    by_cases h : p x <;> simp [h]

omit [Fintype Ω] in
@[simp] theorem restrict_apply (p : Ω → Prop) (f : EuclideanSpace ℝ Ω)
    (x : {x // p x}) : restrict p f x = f x.val := rfl

omit [Fintype Ω] in
@[simp] theorem extend_apply_mem (p : Ω → Prop)
    (f : EuclideanSpace ℝ {x // p x}) (x : Ω) (hx : p x) :
    extend p f x = f ⟨x,hx⟩ := by simp [extend, hx]

omit [Fintype Ω] in
@[simp] theorem extend_apply_not_mem (p : Ω → Prop)
    (f : EuclideanSpace ℝ {x // p x}) (x : Ω) (hx : ¬ p x) :
    extend p f x = 0 := by simp [extend, hx]

omit [Fintype Ω] in
@[simp] theorem restrict_extend (p : Ω → Prop)
    (f : EuclideanSpace ℝ {x // p x}) : restrict p (extend p f) = f := by
  ext x
  simp only [restrict_apply, extend_apply_mem p f x.val x.property]

theorem inner_restrict (p : Ω → Prop) (f : EuclideanSpace ℝ Ω)
    (g : EuclideanSpace ℝ {x // p x}) :
    ⟪restrict p f, g⟫ = ⟪f, extend p g⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  symm
  apply Finset.sum_congr_set (s := {x | p x})
  · intro x hx
    change p x at hx
    rw [restrict_apply, extend_apply_mem p g x hx]
  · intro x hx
    change ¬ p x at hx
    simp [extend, hx]

theorem restrict_starProjection (p : Ω → Prop)
    (S : Submodule ℝ (EuclideanSpace ℝ Ω))
    (T : Submodule ℝ (EuclideanSpace ℝ {x // p x}))
    (hres : ∀ f ∈ S, restrict p f ∈ T)
    (hext : ∀ g ∈ T, extend p g ∈ S)
    (f : EuclideanSpace ℝ Ω) :
    restrict p (S.starProjection f) = T.starProjection (restrict p f) := by
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hres _ (S.starProjection_apply_mem f)
  · intro g hg
    rw [← map_sub, inner_restrict]
    exact Submodule.starProjection_inner_eq_zero f (extend p g) (hext g hg)

variable {K : Type*} [Fintype K]

theorem sum_cells (key : Ω → K) (f : Ω → ℝ) :
    (∑ k, ∑ x : {x // key x = k}, f x.val) = ∑ x, f x := by
  classical
  have h k : (∑ x : {x // key x = k}, f x.val) =
      ∑ x ∈ Finset.univ.filter (fun x => key x = k), f x :=
    (Finset.sum_subtype _ (by simp) f).symm
  simp_rw [h, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem inner_eq_sum_cells (key : Ω → K) (f g : EuclideanSpace ℝ Ω) :
    ⟪f,g⟫ = ∑ k, ⟪restrict (fun x => key x = k) f,
      restrict (fun x => key x = k) g⟫ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, restrict_apply]
  exact (sum_cells key (fun x => g x * f x)).symm

theorem norm_sq_eq_sum_cells (key : Ω → K) (f : EuclideanSpace ℝ Ω) :
    ‖f‖ ^ 2 = ∑ k, ‖restrict (fun x => key x = k) f‖ ^ 2 := by
  simpa only [real_inner_self_eq_norm_sq] using inner_eq_sum_cells key f f

theorem inner_le_norm_sq_of_cells (key : Ω → K)
    (f g : EuclideanSpace ℝ Ω)
    (h : ∀ k, ⟪restrict (fun x => key x = k) f,
      restrict (fun x => key x = k) g⟫ ≤
        ‖restrict (fun x => key x = k) g‖ ^ 2) :
    ⟪f,g⟫ ≤ ‖g‖ ^ 2 := by
  rw [inner_eq_sum_cells key, norm_sq_eq_sum_cells key]
  exact Finset.sum_le_sum (fun k _ => h k)

theorem norm_sq_sum_le_of_cells {ι : Type*} [Fintype ι]
    (key : Ω → K) (f : ι → EuclideanSpace ℝ Ω) (C : ℝ)
    (h : ∀ k, ‖∑ i, restrict (fun x => key x = k) (f i)‖ ^ 2 ≤
      C * ∑ i, ‖restrict (fun x => key x = k) (f i)‖ ^ 2) :
    ‖∑ i, f i‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  rw [norm_sq_eq_sum_cells key]
  simp only [map_sum]
  calc
    _ ≤ ∑ k, C * ∑ i, ‖restrict (fun x => key x = k) (f i)‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => h k)
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [← norm_sq_eq_sum_cells key]

theorem interaction_of_cells (key : Ω → K)
    (f g gain leftError rightError : EuclideanSpace ℝ Ω)
    (h : ∀ k, 2 * ‖restrict (fun x => key x = k) gain‖ ^ 2 -
      ‖restrict (fun x => key x = k) leftError‖ ^ 2 -
      ‖restrict (fun x => key x = k) rightError‖ ^ 2 ≤
      2 * ⟪restrict (fun x => key x = k) f,
        restrict (fun x => key x = k) g⟫) :
    2 * ‖gain‖ ^ 2 - ‖leftError‖ ^ 2 - ‖rightError‖ ^ 2 ≤ 2 * ⟪f,g⟫ := by
  rw [norm_sq_eq_sum_cells key gain, norm_sq_eq_sum_cells key leftError,
    norm_sq_eq_sum_cells key rightError, inner_eq_sum_cells key f g]
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using
    Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => h k)

end Problem315.FiniteCellProjection

end

end OAI
