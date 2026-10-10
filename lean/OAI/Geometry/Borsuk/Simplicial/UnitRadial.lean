import Mathlib
import OAI.Geometry.Borsuk.Simplicial.FineCrossMap

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
open scoped RealInnerProductSpace

noncomputable def unitRadial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) : E :=
  ‖x‖⁻¹ • x

lemma unitRadial_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖unitRadial x‖ = 1 := by
  rw [unitRadial, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma unitRadial_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) :
    unitRadial (-x) = -unitRadial x := by simp [unitRadial]

lemma unitRadial_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : ∀ x ∈ S, x ≠ 0) : ContinuousOn unitRadial S := by
  exact (continuous_norm.continuousOn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (hS x hx))).smul
    continuous_id.continuousOn

lemma odd_sphere_dimension_bound (n m : ℕ) (hn : 0 < n)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) : n ≤ m := by
  by_cases hm : 0 < m
  · have ha : ∀ x ∈ annulus n, x ≠ 0 := by
      intro x hx hzero
      have hn' : (0:ℝ) < n := by exact_mod_cast hn
      have hp : (0:ℝ) < 1/(n:ℝ) := div_pos zero_lt_one hn'
      simp only [annulus, Set.mem_ofPred_eq, hzero, norm_zero] at hx
      linarith [hx.1]
    apply annular_odd_dimension_bound n m hn hm (fun x => f (unitRadial x))
    · exact hf.comp (unitRadial_continuousOn ha) (fun x hx => unitRadial_norm (ha x hx))
    · intro x hx
      exact hfn _ (unitRadial_norm (ha x hx))
    · intro x hx
      rw [unitRadial_neg, hfo _ (unitRadial_norm (ha x hx))]
  · have hm0 : m = 0 := by omega
    subst m
    let x : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0,hn⟩ 1
    have hx : ‖x‖ = 1 := by simp [x]
    have hzero : f x = 0 := Subsingleton.elim _ _
    have hh := hfn x hx
    rw [hzero, norm_zero] at hh
    exact False.elim (zero_ne_one hh)

noncomputable def dropLast (n : ℕ) :
    EuclideanSpace ℝ (Fin (n+1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => x i.castSucc)
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl

lemma dropLast_zero_iff (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    dropLast n x = 0 ↔ x = x (Fin.last n) • EuclideanSpace.single (Fin.last n) 1 := by
  constructor
  · intro hx
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · have hj := congrArg (fun y : EuclideanSpace ℝ (Fin n) => y j) hx
      simpa [dropLast] using hj
  · intro hx
    rw [hx]
    ext i
    simp [dropLast]

lemma dropLast_nonzero (n : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖ = 1)
    (hxp : x ≠ EuclideanSpace.single (Fin.last n) 1)
    (hxm : x ≠ -EuclideanSpace.single (Fin.last n) 1) : dropLast n x ≠ 0 := by
  intro hz
  have he := (dropLast_zero_iff n x).mp hz
  have ha : |x (Fin.last n)| = 1 := by
    conv_rhs => rw [← hx, he]
    simp [norm_smul]
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp ha with hp | hm
  · apply hxp
    simpa [hp] using he
  · apply hxm
    simpa [hm] using he

lemma odd_sphere_surjective (n : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin (n+1)))
    (hf : ContinuousOn f {x | ‖x‖ = 1}) (hfn : ∀ x, ‖x‖ = 1 → ‖f x‖ = 1)
    (hfo : ∀ x, ‖x‖ = 1 → f (-x) = -f x) :
    ∀ y, ‖y‖ = 1 → ∃ x, ‖x‖ = 1 ∧ f x = y := by
  intro y hy
  by_contra hmiss
  push Not at hmiss
  let e : EuclideanSpace ℝ (Fin (n+1)) := EuclideanSpace.single (Fin.last n) 1
  have he : ‖e‖ = 1 := by simp [e]
  let R : EuclideanSpace ℝ (Fin (n+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)) :=
    Submodule.reflection (ℝ ∙ (y-e))ᗮ
  have hRy : R y = e := Submodule.reflection_sub (hy.trans he.symm)
  have hnzero (x : EuclideanSpace ℝ (Fin (n+1))) (hx : ‖x‖ = 1) :
      dropLast n (R (f x)) ≠ 0 := by
    apply dropLast_nonzero n (R (f x)) (by rw [R.norm_map, hfn x hx])
    · intro hp
      exact hmiss x hx (R.injective (hp.trans hRy.symm))
    · intro hm
      have hneg : R (f (-x)) = e := by rw [hfo x hx, map_neg, hm, neg_neg]
      exact hmiss (-x) (by simpa using hx) (R.injective (hneg.trans hRy.symm))
  let g : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n) :=
    fun x => unitRadial (dropLast n (R (f x)))
  have hicont : ContinuousOn (fun x => dropLast n (R (f x))) {x | ‖x‖ = 1} :=
    (dropLast n).continuous_of_finiteDimensional.comp_continuousOn (R.continuous.comp_continuousOn hf)
  have hgc : ContinuousOn g {x | ‖x‖ = 1} := by
    apply (unitRadial_continuousOn (S := {z : EuclideanSpace ℝ (Fin n) | z ≠ 0})
      (fun _ h => h)).comp hicont
    exact fun x hx => hnzero x hx
  have hgn (x) (hx : ‖x‖ = 1) : ‖g x‖ = 1 := unitRadial_norm (hnzero x hx)
  have hgo (x) (hx : ‖x‖ = 1) : g (-x) = -g x := by
    dsimp [g]
    rw [hfo x hx, map_neg, map_neg, unitRadial_neg]
  have hd := odd_sphere_dimension_bound (n+1) n (by omega) g hgc hgn hgo
  omega

end BorsukNine.SimplicialChains

end OAI
