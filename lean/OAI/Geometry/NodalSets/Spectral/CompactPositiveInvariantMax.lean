import OAI.Geometry.NodalSets.Spectral.CompactPositiveMaxEigenvector

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem compact_positive_invariant_max {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (V : Submodule ℝ E) (hV : IsClosed (V : Set E))
    (hInv : ∀ x ∈ V, T x ∈ V) (x : E) (hxV : x ∈ V) (hx : x ≠ 0) :
    ∃ mu > 0, ∃ v : E, v ∈ V ∧ ‖v‖=1 ∧ T v=mu • v ∧
      ∀ y ∈ V, inner ℝ (T y) y ≤ mu*‖y‖^2 := by
  let : CompleteSpace V := hV.completeSpace_coe
  let : Nontrivial V := ⟨⟨⟨x,hxV⟩,0,fun h ↦ hx (congrArg Subtype.val h)⟩⟩
  let S : V →L[ℝ] V := T.restrict hInv
  have hS : S ≠ 0 := by
    intro hz
    have hh : 0 < inner ℝ (S ⟨x,hxV⟩) (⟨x,hxV⟩ : V) := hp x hx
    rw [hz,zero_apply,inner_zero_left] at hh
    exact (lt_irrefl 0) hh
  have hSp : ∀ v : V, 0 ≤ inner ℝ (S v) v := by
    intro v
    by_cases hz : (v : E)=0
    · have hv : v=0 := Subtype.ext hz
      simp only [hv,map_zero,inner_zero_left,le_refl]
    · exact (hp v hz).le
  obtain ⟨v,hvn,hve,hvi,hmax⟩ := compact_positive_max_eigenvector S
    (hc.restrict' hInv) (hs.restrict_invariant hInv) hSp hS
  have hnorm : (0 : ℝ) < ‖S‖ := lt_of_le_of_ne (norm_nonneg S)
    (fun hz ↦ hS ((ContinuousLinearMap.opNorm_zero_iff S).mp hz.symm))
  refine ⟨‖S‖,hnorm,(v : E),v.property,hvn,?_,?_⟩
  · exact congrArg Subtype.val hve
  · intro y hy
    exact hmax ⟨y,hy⟩

end
end Yau.Analysis

end OAI
