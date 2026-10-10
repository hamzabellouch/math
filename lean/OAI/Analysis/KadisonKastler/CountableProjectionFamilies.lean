import OAI.Analysis.KadisonKastler.Algebra
import OAI.Analysis.FactorGeneration.DyadicComparison
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! # Countable projection families from separating vectors

The spatial derivation argument needs countable decomposability of the
algebra, rather than separability of the ambient Hilbert space. A
countable family of separating vectors supplies exactly this property.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped BigOperators

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def HasCountableProjectionFamilies (M : VonNeumannAlgebra H) : Prop :=
  ∀ (ι : Type u) (p : ι → AlgebraProjection M),
    (∀ i, (p i).val ≠ 0) →
    Pairwise (fun i j => (p i).val * (p j).val = 0) → Countable ι

theorem projection_norm_apply_sq (p : AlgebraProjection M) (ξ : H) :
    ‖p.val.val ξ‖ ^ 2 = (inner ℂ (p.val.val ξ) ξ).re := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left p.val.val ξ
  change ‖p.val.val ξ‖ ^ 2 = (inner ℂ ((star p.val.val * p.val.val) ξ) ξ).re at h
  simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using h

theorem countable_projection_vector_support {ι : Type*}
    (p : ι → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) (ξ : H) :
    {i | (p i).val.val ξ ≠ 0}.Countable := by
  classical
  have hsum (s : Finset ι) : ∑ i ∈ s, ‖(p i).val.val ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    let q := AlgebraProjection.finsetSum p s (fun _ _ _ _ hij => ho hij)
    have hqsum : q.val.val ξ = ∑ i ∈ s, (p i).val.val ξ := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) ξ = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    have he : ∑ i ∈ s, ‖(p i).val.val ξ‖ ^ 2 = ‖q.val.val ξ‖ ^ 2 := by
      calc
        _ = ∑ i ∈ s, (inner ℂ ((p i).val.val ξ) ξ).re := by
          simp only [projection_norm_apply_sq]
        _ = (inner ℂ (∑ i ∈ s, (p i).val.val ξ) ξ).re := by
          simp only [sum_inner, Complex.re_sum]
        _ = (inner ℂ (q.val.val ξ) ξ).re := by rw [hqsum]
        _ = ‖q.val.val ξ‖ ^ 2 := (projection_norm_apply_sq q ξ).symm
    have hqn : ‖q.val.val ξ‖ ≤ ‖ξ‖ := by
      calc
        ‖q.val.val ξ‖ ≤ ‖q.val.val‖ * ‖ξ‖ := q.val.val.le_opNorm ξ
        _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right
          (IsStarProjection.norm_le _ (q.property.map M.toStarSubalgebra.subtype)) (norm_nonneg ξ)
        _ = ‖ξ‖ := one_mul _
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) hqn 2
  have hs : Summable (fun i => ‖(p i).val.val ξ‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hsum
  have he : Function.support (fun i => ‖(p i).val.val ξ‖ ^ 2) =
      {i | (p i).val.val ξ ≠ 0} := by
    ext i
    simp [Function.support]
  rw [← he]
  exact hs.countable_support

theorem countableProjectionFamilies_of_separating_vectors
    (ξ : ℕ → H)
    (hξ : ∀ a : Algebra M, (∀ n, a.val (ξ n) = 0) → a = 0) :
    HasCountableProjectionFamilies M := by
  intro ι p hp ho
  have hcover : (Set.univ : Set ι) ⊆ ⋃ n, {i | (p i).val.val (ξ n) ≠ 0} := by
    intro i _
    have hn : ∃ n, (p i).val.val (ξ n) ≠ 0 := by
      by_contra h
      push Not at h
      exact hp i (hξ (p i).val h)
    obtain ⟨n, hn⟩ := hn
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  exact Set.countable_univ_iff.mp
    ((Set.countable_iUnion (fun n => countable_projection_vector_support p ho (ξ n))).mono hcover)

end

end KadisonKastler

end OAI
