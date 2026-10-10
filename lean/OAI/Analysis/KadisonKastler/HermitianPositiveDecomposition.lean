import OAI.Analysis.BoundedHochschild.PositiveDecomposition
import OAI.Analysis.KadisonKastler.HermitianLinearExtension
import OAI.Analysis.Naimark.States

namespace OAI

/-! # Norm-additive positive decomposition of a Hermitian functional

The real Hahn–Banach pair construction already in the library gives the
positive and negative parts with the exact total norm needed by Sakai's
extreme-functional argument.
-/

namespace KadisonKastler

noncomputable section

open HochschildPositiveDecomposition NaimarkZFC
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]

theorem exists_norm_additive_positive_decomposition (f : A →L[ℂ] ℂ)
    (hf : ∀ a, f (star a) = star (f a)) :
    ∃ p q : A →ₚ[ℂ] ℂ, (∀ a, f a = p a - q a) ∧
      (p 1).re + (q 1).re = ‖f‖ := by
  let l := realRestriction f
  obtain ⟨g, hgn, hg1, hgl⟩ := exists_pair_extension l
  let p₀ := g.comp (ContinuousLinearMap.inl ℝ (selfAdjoint A) (selfAdjoint A))
  let q₀ := g.comp (ContinuousLinearMap.inr ℝ (selfAdjoint A) (selfAdjoint A))
  have hp₀ (a : selfAdjoint A) (ha : 0 ≤ (a : A)) : 0 ≤ p₀ a :=
    pair_nonneg g (norm_nonneg l) hgn hg1 a 0 ha (by simp)
  have hq₀ (a : selfAdjoint A) (ha : 0 ≤ (a : A)) : 0 ≤ q₀ a :=
    pair_nonneg g (norm_nonneg l) hgn hg1 0 a (by simp) ha
  let p := complexifyPositive p₀.toLinearMap hp₀
  let q := complexifyPositive q₀.toLinearMap hq₀
  have hdiff (a : selfAdjoint A) : l a = p₀ a - q₀ a := by
    rw [← hgl]
    change g (a, -a) = g (a, 0) - g (0, a)
    rw [← map_sub]
    congr 1
    simp
  have heq : f.toLinearMap = p.toLinearMap - q.toLinearMap := by
    apply complexLinear_eq_of_selfAdjoint
    intro a
    change f (a : A) = p (a : A) - q (a : A)
    rw [complexifyPositive_apply, complexifyPositive_apply,
      complexify_selfAdjoint, complexify_selfAdjoint]
    have hi := congrArg Complex.im (hf (a : A))
    rw [a.property.star_eq, Complex.star_def, Complex.conj_im] at hi
    apply Complex.ext
    · exact hdiff a
    · simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      linarith
  have hsum : (p 1).re + (q 1).re = ‖l‖ := by
    change (complexify p₀.toLinearMap ((1 : selfAdjoint A) : A)).re +
      (complexify q₀.toLinearMap ((1 : selfAdjoint A) : A)).re = ‖l‖
    rw [complexify_selfAdjoint, complexify_selfAdjoint]
    change g (1, 0) + g (0, 1) = ‖l‖
    rw [← map_add]
    simpa using hg1
  have hfbound : ‖f‖ ≤ ‖l‖ := by
    apply f.opNorm_le_bound (norm_nonneg l)
    intro a
    have ha : f a = p a - q a := congrArg (fun F : A →ₗ[ℂ] ℂ => F a) heq
    rw [ha]
    calc
      ‖p a - q a‖ ≤ ‖p a‖ + ‖q a‖ := norm_sub_le _ _
      _ ≤ (p 1).re * ‖a‖ + (q 1).re * ‖a‖ :=
        add_le_add (positive_norm_apply_le p a) (positive_norm_apply_le q a)
      _ = ‖l‖ * ‖a‖ := by rw [← add_mul, hsum]
  have hn : ‖l‖ = ‖f‖ := le_antisymm (realRestriction_norm f) hfbound
  refine ⟨p, q, ?_, hsum.trans hn⟩
  intro a
  exact congrArg (fun F : A →ₗ[ℂ] ℂ => F a) heq

end

end KadisonKastler

end OAI
