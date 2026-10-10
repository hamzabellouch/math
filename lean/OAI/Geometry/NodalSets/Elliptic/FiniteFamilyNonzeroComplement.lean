import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import OAI.Geometry.NodalSets.Spectral.CompactEigenfamilyComplement

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem finite_family_nonzero_complement {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Finite I]
    (hE : ¬FiniteDimensional ℝ E) (e : I → E) :
    ∃ x : E, x ∈ (Submodule.span ℝ (range e))ᗮ ∧ x ≠ 0 := by
  let V := Submodule.span ℝ (range e)
  let : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (finite_range e)
  have hV : V ≠ ⊤ := by
    intro h
    apply hE
    apply FiniteDimensional.of_surjective V.subtype
    intro x
    exact ⟨⟨x,by rw [h]; trivial⟩,rfl⟩
  have horth : Vᗮ ≠ ⊥ := fun h ↦ hV (Submodule.orthogonal_eq_bot_iff.mp h)
  exact Submodule.exists_mem_ne_zero_of_ne_bot horth

theorem compact_positive_finite_family_extension {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [Finite I]
    (hE : ¬FiniteDimensional ℝ E)
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i) :
    ∃ lam > 0, ∃ v : E, ‖v‖=1 ∧ T v=lam • v ∧
      (∀ i, inner ℝ (e i) v=0) ∧
      (∀ y ∈ (Submodule.span ℝ (range e))ᗮ, inner ℝ (T y) y ≤ lam*‖y‖^2) := by
  obtain ⟨x,hx,hx0⟩ := finite_family_nonzero_complement hE e
  exact compact_positive_eigenfamily_extension T hc hs hp e mu he x hx hx0

end
end Yau.Analysis

end OAI
