import Mathlib
import OAI.Geometry.TamingCompatibility.Model

namespace OAI

noncomputable section
open scoped Manifold ContDiff
namespace TamingCompatibility

variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X]
  [IsManifold Model ∞ X]

theorem Tames.isNondegenerate {α : TwoForm X} {J : AlmostComplexStructure X}
    (h : Tames α J) : IsNondegenerate α := by
  intro x v hv
  by_contra hn
  exact (ne_of_gt (h x v hn)) (hv (J.endomorphism x v))

omit [IsManifold Model ∞ X] in
lemma eval_swap (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x v u = -eval α x u v := by
  have hs : (![u, v] ∘ Equiv.swap (0 : Fin 2) 1) = ![v, u] := by
    funext i
    fin_cases i <;> simp
  simpa only [eval, hs, ContinuousAlternatingMap.coe_toAlternatingMap] using
    (α x).toAlternatingMap.map_swap ![u, v] (show (0 : Fin 2) ≠ 1 by decide)

omit [IsManifold Model ∞ X] in
lemma eval_neg_left (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x (-u) v = -eval α x u v := by
  simpa only [neg_one_smul, smul_eq_mul, neg_one_mul, eval] using
    (α x).vecCons_smul ![v] (-1 : ℝ) u

omit [IsManifold Model ∞ X] in
lemma eval_neg_right (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x u (-v) = -eval α x u v := by
  rw [eval_swap, eval_neg_left, eval_swap, neg_neg]

omit [IsManifold Model ∞ X] in
lemma eval_neg_neg (α : TwoForm X) (x : X) (u v : TangentSpace Model x) :
    eval α x (-u) (-v) = eval α x u v := by
  rw [eval_neg_left, eval_neg_right, neg_neg]

def jAction (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  fun x => (α x).compContinuousLinearMap (J.endomorphism x)

lemma eval_jAction (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    eval (jAction J α) x u v =
      eval α x (J.endomorphism x u) (J.endomorphism x v) := by
  simp only [eval, jAction, ContinuousAlternatingMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

def invariantPart (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  (1 / 2 : ℝ) • (α + jAction J α)

def antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) : TwoForm X :=
  (1 / 2 : ℝ) • (α - jAction J α)

lemma eval_invariantPart (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    eval (invariantPart J α) x u v =
      (eval α x u v + eval α x (J.endomorphism x u) (J.endomorphism x v)) / 2 := by
  change (1 / 2 : ℝ) * (eval α x u v + eval (jAction J α) x u v) = _
  rw [eval_jAction]
  ring

lemma invariantPart_isInvariant (J : AlmostComplexStructure X) (α : TwoForm X) :
    IsInvariant (invariantPart J α) J := by
  intro x u v
  rw [eval_invariantPart, eval_invariantPart, J.square, J.square, eval_neg_neg, add_comm]

lemma eval_invariantPart_complexLine (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (v : TangentSpace Model x) :
    eval (invariantPart J α) x v (J.endomorphism x v) =
      eval α x v (J.endomorphism x v) := by
  rw [eval_invariantPart, J.square, eval_neg_right]
  rw [eval_swap α x v (J.endomorphism x v), neg_neg]
  ring

lemma tames_invariantPart {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : Tames α J) : Tames (invariantPart J α) J := by
  intro x v hv
  rw [eval_invariantPart_complexLine]
  exact h x v hv

lemma compatible_invariantPart {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : Tames α J) : Compatible (invariantPart J α) J :=
  ⟨tames_invariantPart h, invariantPart_isInvariant J α⟩
omit [IsManifold Model ∞ X] in
lemma TwoForm.ext_eval {α β : TwoForm X}
    (h : ∀ x u v, eval α x u v = eval β x u v) : α = β := by
  funext x
  ext v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  simpa only [eval, ← hv] using h x (v 0) (v 1)

lemma jAction_involutive (J : AlmostComplexStructure X) :
    Function.Involutive (jAction J) := by
  intro α
  apply TwoForm.ext_eval
  intro x u v
  rw [eval_jAction, eval_jAction, J.square, J.square, eval_neg_neg]

lemma jAction_add (J : AlmostComplexStructure X) (α β : TwoForm X) :
    jAction J (α + β) = jAction J α + jAction J β := rfl

lemma jAction_smul (J : AlmostComplexStructure X) (c : ℝ) (α : TwoForm X) :
    jAction J (c • α) = c • jAction J α := rfl

lemma invariantPart_add_antiInvariantPart (J : AlmostComplexStructure X) (α : TwoForm X) :
    invariantPart J α + antiInvariantPart J α = α := by
  unfold invariantPart antiInvariantPart
  module

lemma invariantPart_idempotent (J : AlmostComplexStructure X) (α : TwoForm X) :
    invariantPart J (invariantPart J α) = invariantPart J α := by
  unfold invariantPart
  rw [jAction_smul, jAction_add, jAction_involutive J α]
  module

lemma antiInvariantPart_idempotent (J : AlmostComplexStructure X) (α : TwoForm X) :
    antiInvariantPart J (antiInvariantPart J α) = antiInvariantPart J α := by
  have hneg (β : TwoForm X) : jAction J (-β) = -jAction J β := rfl
  unfold antiInvariantPart
  simp only [sub_eq_add_neg, jAction_smul, jAction_add, hneg, jAction_involutive J α]
  module

lemma AlmostComplexStructure.injective (J : AlmostComplexStructure X) (x : X) :
    Function.Injective (J.endomorphism x) := by
  intro u v h
  have h' := congrArg (J.endomorphism x) h
  simpa only [J.square, neg_inj] using h'

lemma AlmostComplexStructure.surjective (J : AlmostComplexStructure X) (x : X) :
    Function.Surjective (J.endomorphism x) := by
  intro v
  refine ⟨-J.endomorphism x v, ?_⟩
  rw [map_neg, J.square, neg_neg]

omit [IsManifold Model ∞ X] in
lemma pullback_add (α β : TwoForm X) (f : Space → X) :
    pullback (α + β) f = pullback α f + pullback β f := rfl

omit [IsManifold Model ∞ X] in
lemma pullback_smul (c : ℝ) (α : TwoForm X) (f : Space → X) :
    pullback (c • α) f = c • pullback α f := rfl

omit [IsManifold Model ∞ X] in
lemma IsSmooth.zero : IsSmooth (0 : TwoForm X) := by
  intro f U hU hf
  change ContDiffOn ℝ ∞ (fun _ : Space => (0 : Space [⋀^Fin 2]→L[ℝ] ℝ)) U
  exact contDiffOn_const

omit [IsManifold Model ∞ X] in
lemma IsSmooth.add {α β : TwoForm X} (hα : IsSmooth α) (hβ : IsSmooth β) :
    IsSmooth (α + β) := by
  intro f U hU hf
  rw [pullback_add]
  exact (hα f U hU hf).add (hβ f U hU hf)

omit [IsManifold Model ∞ X] in
lemma IsSmooth.smul (c : ℝ) {α : TwoForm X} (hα : IsSmooth α) :
    IsSmooth (c • α) := by
  intro f U hU hf
  rw [pullback_smul]
  exact (hα f U hU hf).const_smul c

omit [IsManifold Model ∞ X] in
lemma IsClosed.zero : IsClosed (0 : TwoForm X) := by
  intro f U hU hf y hy
  change extDerivWithin (fun _ => (0 : Space [⋀^Fin 2]→L[ℝ] ℝ)) U y = 0
  rw [extDerivWithin, fderivWithin_fun_const]
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ Space ℝ 0 = 0
  exact map_zero _

omit [IsManifold Model ∞ X] in
lemma IsClosed.add {α β : TwoForm X} (hα : IsClosed α) (hβ : IsClosed β)
    (hαs : IsSmooth α) (hβs : IsSmooth β) : IsClosed (α + β) := by
  intro f U hU hf y hy
  rw [pullback_add, extDerivWithin_add (hU.uniqueDiffWithinAt hy)]
  · rw [hα f U hU hf y hy, hβ f U hU hf y hy, add_zero]
  · exact ((hαs f U hU hf).differentiableOn (by norm_num)) y hy
  · exact ((hβs f U hU hf).differentiableOn (by norm_num)) y hy

omit [IsManifold Model ∞ X] in
lemma IsClosed.smul (c : ℝ) {α : TwoForm X} (hα : IsClosed α) :
    IsClosed (c • α) := by
  intro f U hU hf y hy
  rw [pullback_smul, extDerivWithin_smul c _ (hU.uniqueDiffWithinAt hy),
    hα f U hU hf y hy, smul_zero]

def smoothClosedInvariantForms (J : AlmostComplexStructure X) : Submodule ℝ (TwoForm X) where
  carrier := {α | IsSmooth α ∧ IsClosed α ∧ IsInvariant α J}
  zero_mem' := ⟨IsSmooth.zero, IsClosed.zero, fun _ _ _ => rfl⟩
  add_mem' := by
    intro α β hα hβ
    refine ⟨hα.1.add hβ.1, hα.2.1.add hβ.2.1 hα.1 hβ.1, ?_⟩
    intro x u v
    change eval α x (J.endomorphism x u) (J.endomorphism x v) +
      eval β x (J.endomorphism x u) (J.endomorphism x v) = _
    rw [hα.2.2, hβ.2.2]
    rfl
  smul_mem' := by
    intro c α hα
    refine ⟨hα.1.smul c, hα.2.1.smul c, ?_⟩
    intro x u v
    change c * eval α x (J.endomorphism x u) (J.endomorphism x v) = _
    rw [hα.2.2]
    rfl

lemma convex_taming_forms (J : AlmostComplexStructure X) :
    Convex ℝ {α : TwoForm X | Tames α J} := by
  intro α hα β hβ a b ha hb hab x v hv
  have hαv := hα x v hv
  have hβv := hβ x v hv
  change 0 < a * eval α x v (J.endomorphism x v) +
    b * eval β x v (J.endomorphism x v)
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hβv
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hαv)
      (mul_nonneg hb hβv.le)

def associatedBilinear (J : AlmostComplexStructure X) (α : TwoForm X) (x : X) :
    TangentSpace Model x →L[ℝ] TangentSpace Model x →L[ℝ] ℝ := by
  letI : NormedAddCommGroup (TangentSpace Model x) := inferInstanceAs (NormedAddCommGroup Space)
  letI : NormedSpace ℝ (TangentSpace Model x) := inferInstanceAs (NormedSpace ℝ Space)
  exact ((ContinuousLinearMap.compL ℝ (TangentSpace Model x) (TangentSpace Model x) ℝ).flip
      (J.endomorphism x)) ∘L
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := TangentSpace Model x) (F := ℝ)
      (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L (α x).curryLeft)

lemma associatedBilinear_apply (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x u v = eval α x u (J.endomorphism x v) := by
  change (α x) (Matrix.vecCons u (fun _ : Fin 1 => J.endomorphism x v)) =
    (α x) ![u, J.endomorphism x v]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma IsInvariant.shift_J {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    eval α x (J.endomorphism x u) v = -eval α x u (J.endomorphism x v) := by
  have he := h x u (J.endomorphism x v)
  rw [J.square, eval_neg_right] at he
  linarith

lemma IsInvariant.associatedBilinear_symm {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x u v = associatedBilinear J α x v u := by
  simp only [associatedBilinear_apply]
  calc
    eval α x u (J.endomorphism x v) = -eval α x (J.endomorphism x u) v := by
      rw [h.shift_J x u v, neg_neg]
    _ = eval α x v (J.endomorphism x u) := (eval_swap α x (J.endomorphism x u) v).symm

lemma IsInvariant.associatedBilinear_hermitian {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : IsInvariant α J) (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J α x (J.endomorphism x u) (J.endomorphism x v) =
      associatedBilinear J α x u v := by
  rw [associatedBilinear_apply, associatedBilinear_apply]
  exact h x u (J.endomorphism x v)

lemma Tames.associatedBilinear_pos {J : AlmostComplexStructure X} {α : TwoForm X}
    (h : Tames α J) (x : X) (v : TangentSpace Model x) (hv : v ≠ 0) :
    0 < associatedBilinear J α x v v := by
  rw [associatedBilinear_apply]
  exact h x v hv

lemma associatedBilinear_invariantPart_fundamental
    (J : AlmostComplexStructure X) (α : TwoForm X)
    (x : X) (u v : TangentSpace Model x) :
    associatedBilinear J (invariantPart J α) x (J.endomorphism x u) v =
      eval (invariantPart J α) x u v := by
  rw [associatedBilinear_apply]
  exact invariantPart_isInvariant J α x u v

end TamingCompatibility

open scoped Manifold ContDiff Topology
open Filter Set

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

end

end OAI
