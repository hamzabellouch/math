import Mathlib

namespace OAI

/-! Continuous linear identities and commutation extend from a dense sequence
in the positive cone, which linearly spans a C*-algebra. -/

noncomputable section

namespace WeakPureInfiniteness

variable {D E : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
  [NonUnitalCStarAlgebra E]

omit [StarOrderedRing D] in
lemma exists_dense_positive_sequence [TopologicalSpace.SeparableSpace D] :
    ∃ p : ℕ → {x : D // 0 ≤ x}, DenseRange p := by
  let : Nonempty {x : D // 0 ≤ x} := ⟨⟨0, le_rfl⟩⟩
  exact TopologicalSpace.exists_dense_seq _

lemma continuousLinearMap_ext_positive_sequence (p : ℕ → {x : D // 0 ≤ x})
    (hp : DenseRange p) (f g : D →L[ℂ] E) (he : ∀ n, f (p n) = g (p n)) : f = g := by
  have hpos (x : {x : D // 0 ≤ x}) : f x = g x := by
    exact congrFun (hp.equalizer (f.continuous.comp continuous_subtype_val)
      (g.continuous.comp continuous_subtype_val) (funext he)) x
  have hspan : Submodule.span ℂ {x : D | 0 ≤ x} ≤ LinearMap.eqLocus f.toLinearMap g.toLinearMap :=
    Submodule.span_le.mpr (fun x hx => hpos ⟨x, hx⟩)
  rw [CStarAlgebra.span_nonneg] at hspan
  ext x
  exact hspan (Submodule.mem_top)

lemma commute_of_positive_sequence (p : ℕ → {x : D // 0 ≤ x})
    (hp : DenseRange p) (T : D →L[ℂ] E) (x : E)
    (he : ∀ n, Commute (T (p n)) x) (d : D) : Commute (T d) x := by
  have hmaps : ((ContinuousLinearMap.mul ℂ E).flip x).comp T =
      (ContinuousLinearMap.mul ℂ E x).comp T :=
    continuousLinearMap_ext_positive_sequence p hp _ _ (fun n => (he n).eq)
  exact congrArg (fun f : D →L[ℂ] E => f d) hmaps

lemma abelian_range_of_positive_sequence (p : ℕ → {x : D // 0 ≤ x})
    (hp : DenseRange p) (T : D →L[ℂ] E)
    (he : ∀ n m, Commute (T (p n)) (T (p m))) (x y : D) : Commute (T x) (T y) := by
  have hfirst (n : ℕ) (y : D) : Commute (T (p n)) (T y) :=
    (commute_of_positive_sequence p hp T (T (p n)) (fun m => (he n m).symm) y).symm
  exact commute_of_positive_sequence p hp T (T y) (fun n => hfirst n y) x

end WeakPureInfiniteness

end

end OAI
