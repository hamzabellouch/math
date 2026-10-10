import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.NoncommRing

namespace OAI

/-! # Infinitesimal commutators of matrix groups

The finite-dimensional span of derivatives of curves in a subgroup records
its infinitesimal action. Differentiating group commutators twice puts the
algebra commutator into the tangent span of the derived subgroup.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Topology commutatorElement
open Filter

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [FiniteDimensional ℝ A] [CompleteSpace A]

/-- A derivative at the identity of a curve contained in a given matrix group. -/
def AlgebraGroupTangentVector (D : Subgroup Aˣ) (X : A) : Prop :=
  ∃ c : ℝ → Aˣ, (∀ t, c t ∈ D) ∧ c 0 = 1 ∧
    HasDerivAt (fun t => (c t : A)) X 0

/-- The finite-dimensional linear span of the actual curve derivatives. -/
def algebraGroupTangentSpan (D : Subgroup Aˣ) : Submodule ℝ A :=
  Submodule.span ℝ {X | AlgebraGroupTangentVector D X}

omit [FiniteDimensional ℝ A] in
/-- Differentiating an inverse curve at the identity negates the tangent. -/
theorem hasDerivAt_units_inverse_at_one {c : ℝ → Aˣ} {X : A}
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => (c t : A)) X 0) :
    HasDerivAt (fun t => (((c t)⁻¹ : Aˣ) : A)) (-X) 0 := by
  have h := (hasFDerivAt_ringInverse (𝕜 := ℝ) (c 0)).comp_hasDerivAt 0 hc
  simpa only [Function.comp_def, Ring.inverse_unit, h0, inv_one, Units.val_one,
    neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    one_mul, mul_one] using h

omit [CompleteSpace A] in
/-- A derivative of a curve in a finite-dimensional linear subspace stays
in that subspace. -/
theorem submodule_mem_of_hasDerivAt (M : Submodule ℝ A) {f : ℝ → A} {X : A}
    (hf : HasDerivAt f X 0) (hmem : ∀ t, f t ∈ M) : X ∈ M := by
  exact M.closed_of_finiteDimensional.mem_of_tendsto hf.tendsto_slope
    (Filter.Eventually.of_forall (fun t => M.smul_mem _ (M.sub_mem (hmem t) (hmem 0))))

omit [FiniteDimensional ℝ A] [CompleteSpace A] in
theorem algebraGroupTangentSpan_mono {D F : Subgroup Aˣ} (hDF : D ≤ F) :
    algebraGroupTangentSpan D ≤ algebraGroupTangentSpan F := by
  apply Submodule.span_mono
  rintro X ⟨c, hc, h0, hd⟩
  exact ⟨c, fun t => hDF (hc t), h0, hd⟩

omit [FiniteDimensional ℝ A] [CompleteSpace A] in
/-- The identity group has zero tangent span. -/
theorem algebraGroupTangentSpan_bot : algebraGroupTangentSpan (⊥ : Subgroup Aˣ) = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.mpr
  rintro X ⟨c, hc, _, hd⟩
  have hfun : (fun t => (c t : A)) = fun _ => (1 : A) := by
    funext t
    rw [show c t = 1 from hc t]
    rfl
  rw [hfun] at hd
  exact hd.unique (hasDerivAt_const 0 (1 : A))

omit [FiniteDimensional ℝ A] in
/-- Conjugation by one group element gives a tangent of the group commutator
subgroup after subtracting the original tangent. -/
theorem conjugation_difference_tangent {D : Subgroup Aˣ} {u : Aˣ} (hu : u ∈ D)
    {Y : A} (hY : AlgebraGroupTangentVector D Y) :
    AlgebraGroupTangentVector ⁅D, D⁆ ((u : A) * Y * (u⁻¹ : Aˣ) - Y) := by
  obtain ⟨c, hc, h0, hd⟩ := hY
  refine ⟨fun t => ⁅u, c t⁆, fun t => Subgroup.commutator_mem_commutator hu (hc t), ?_, ?_⟩
  · simp only [h0, commutatorElement_def, mul_one, mul_inv_cancel]
  · have hi := hasDerivAt_units_inverse_at_one h0 hd
    have h := (((hasDerivAt_const 0 (u : A)).mul hd).mul
      (hasDerivAt_const (0 : ℝ) ((u⁻¹ : Aˣ) : A))).mul hi
    convert h using 1
    simp [h0, sub_eq_add_neg]

/-- Two actual tangents have an algebra commutator tangent to the derived
subgroup. The second differentiation uses closedness of the finite span. -/
theorem commutator_mem_derived_tangentSpan {D : Subgroup Aˣ} {X Y : A}
    (hX : AlgebraGroupTangentVector D X) (hY : AlgebraGroupTangentVector D Y) :
    X * Y - Y * X ∈ algebraGroupTangentSpan ⁅D, D⁆ := by
  obtain ⟨c, hc, h0, hd⟩ := hX
  have hi := hasDerivAt_units_inverse_at_one h0 hd
  have hdiff : HasDerivAt (fun t => (c t : A) * Y * ((c t)⁻¹ : Aˣ) - Y)
      (X * Y - Y * X) 0 := by
    have h := ((hd.mul_const Y).mul hi).sub_const Y
    simpa [h0, sub_eq_add_neg] using h
  apply submodule_mem_of_hasDerivAt (algebraGroupTangentSpan ⁅D, D⁆) hdiff
  intro t
  exact Submodule.subset_span (conjugation_difference_tangent (hc t) hY)

end PolycyclicRecognition

end

end OAI
