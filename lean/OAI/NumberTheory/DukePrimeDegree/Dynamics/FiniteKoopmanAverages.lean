import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicAverageMean
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Topology.Algebra.MulAction

namespace OAI

/-!
# Finite averages of Koopman operators

An average of finitely many Hilbert-space isometries has exactly their
common fixed vectors. This permits averaging an entire generating
family of an ergodic action without asserting that one chosen group
element is ergodic.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace DukePrimeDegree

section Hilbert

variable {I E : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Nonempty I] in
lemma eq_of_equal_norms_and_barycenter
    (w : I → E) (v : E) (hnorm : ∀ i, ‖w i‖ = ‖v‖)
    (hsum : (∑ i, w i) = (Fintype.card I : ℝ) • v) :
    ∀ i, w i = v := by
  classical
  have hinn : (∑ i, inner ℝ (w i) v) = (Fintype.card I : ℝ) * ‖v‖ ^ 2 := by
    rw [← sum_inner, hsum, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hsq : (∑ i, ‖w i - v‖ ^ 2) = 0 := by
    calc
      _ = ∑ i, (‖v‖ ^ 2 - 2 * inner ℝ (w i) v + ‖v‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_sub_sq_real, hnorm i]
      _ = (Fintype.card I : ℝ) * ‖v‖ ^ 2 -
          2 * (∑ i, inner ℝ (w i) v) + (Fintype.card I : ℝ) * ‖v‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = 0 := by rw [hinn]; ring
  intro i
  have hi : ‖w i - v‖ ^ 2 ≤ 0 := by
    rw [← hsq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖w j - v‖) (Finset.mem_univ i)
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))))

def finiteIsometryAverage (U : I → E →L[ℝ] E) : E →L[ℝ] E :=
  (Fintype.card I : ℝ)⁻¹ • ∑ i, U i

omit [Nonempty I] in
lemma finiteIsometryAverage_apply (U : I → E →L[ℝ] E) (v : E) :
    finiteIsometryAverage U v = (Fintype.card I : ℝ)⁻¹ • ∑ i, U i v := by
  simp [finiteIsometryAverage]

theorem finiteIsometryAverage_fixed_iff (U : I → E →L[ℝ] E)
    (hU : ∀ i v, ‖U i v‖ = ‖v‖) (v : E) :
    finiteIsometryAverage U v = v ↔ ∀ i, U i v = v := by
  classical
  have hcard : (Fintype.card I : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  constructor
  · intro hv
    have hh := congrArg (fun z : E => (Fintype.card I : ℝ) • z) hv
    rw [finiteIsometryAverage_apply, smul_smul, mul_inv_cancel₀ hcard, one_smul] at hh
    exact eq_of_equal_norms_and_barycenter (fun i => U i v) v (fun i => hU i v) hh
  · intro hv
    rw [finiteIsometryAverage_apply]
    simp only [hv, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

theorem finiteIsometryAverage_norm_le (U : I → E →L[ℝ] E)
    (hU : ∀ i v, ‖U i v‖ = ‖v‖) : ‖finiteIsometryAverage U‖ ≤ 1 := by
  classical
  have hc : 0 < (Fintype.card I : ℝ) := by exact_mod_cast Fintype.card_pos
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul, finiteIsometryAverage_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hc)]
  calc
    _ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, ‖U i v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
    _ = ‖v‖ := by
      simp only [hU, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end Hilbert

section DenseGenerators

variable {G Y I : Type*} [Group G] [TopologicalSpace G]
  [TopologicalSpace Y] [T2Space Y] [MulAction G Y] [ContinuousSMul G Y]

/-- Continuity extends fixedness under a finite or infinite generating
family to fixedness under the full group when its algebraic closure is
dense. This will be applied to the continuous L2 domain action. -/
theorem fixed_of_dense_generators (a : I → G)
    (hdense : Dense (Subgroup.closure (range a) : Set G))
    (v : Y) (hfix : ∀ i, a i • v = v) : ∀ g : G, g • v = v := by
  have hc : IsClosed (MulAction.stabilizer G v : Set G) :=
    isClosed_eq (continuous_id.smul continuous_const) continuous_const
  have hle : Subgroup.closure (range a) ≤ MulAction.stabilizer G v := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i, rfl⟩
    exact hfix i
  have hcl := closure_minimal hle hc
  intro g
  exact hcl (hdense g)

end DenseGenerators

section GroupAction

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
  (μ : Measure X) [ErgodicSMul G X μ]

/-- Group ergodicity supplies constant invariant observables directly;
no selected element is assumed ergodic. -/
theorem ae_eq_const_of_group_invariant (f : X → ℝ)
    (hf : AEStronglyMeasurable f μ)
    (hinv : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] f) :
    ∃ c : ℝ, f =ᵐ[μ] fun _ => c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro U hU
  apply eventuallyEmptyOrUniv_iff.mp
  apply aeconst_of_forall_preimage_smul_ae_eq G (hf.aemeasurable.nullMeasurable hU)
  intro g
  refine ((hinv g).mono fun x hx => ?_).set_eq
  simp only [Set.mem_preimage, hx]

end GroupAction
end DukePrimeDegree

end

end OAI
