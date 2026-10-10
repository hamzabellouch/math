import OAI.Geometry.NodalSets.Spectral.CompactPositiveInvariantMax

namespace OAI

namespace Yau.Analysis
open Set
noncomputable section

theorem eigenfamily_orthogonal_invariant {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →L[ℝ] E) (hs : T.IsSymmetric)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i) :
    ∀ x ∈ (Submodule.span ℝ (range e))ᗮ, T x ∈ (Submodule.span ℝ (range e))ᗮ := by
  intro x hx y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,rfl⟩ := hy
    have hh := hx (e i) (Submodule.subset_span (mem_range_self i))
    have hsym : inner ℝ (T (e i)) x = inner ℝ (e i) (T x) := hs (e i) x
    rw [← hsym,he i,inner_smul_left_eq_smul,smul_eq_mul,hh,mul_zero]
  | zero => exact inner_zero_left _
  | add y z hy hz ihy ihz => rw [inner_add_left,ihy,ihz,add_zero]
  | smul a y hy ih => rw [inner_smul_left_eq_smul,smul_eq_mul,ih,mul_zero]

theorem compact_positive_eigenfamily_extension {E I : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hc : IsCompactOperator T) (hs : T.IsSymmetric)
    (hp : ∀ x : E, x ≠ 0 → 0 < inner ℝ (T x) x)
    (e : I → E) (mu : I → ℝ) (he : ∀ i, T (e i)=mu i • e i)
    (x : E) (hx : x ∈ (Submodule.span ℝ (range e))ᗮ) (hx0 : x ≠ 0) :
    ∃ lam > 0, ∃ v : E, ‖v‖=1 ∧ T v=lam • v ∧
      (∀ i, inner ℝ (e i) v=0) ∧
      (∀ y ∈ (Submodule.span ℝ (range e))ᗮ, inner ℝ (T y) y ≤ lam*‖y‖^2) := by
  obtain ⟨lam,hlam,v,hv,hvn,hve,hmax⟩ := compact_positive_invariant_max T hc hs hp
    (Submodule.span ℝ (range e))ᗮ (Submodule.isClosed_orthogonal _)
    (eigenfamily_orthogonal_invariant T hs e mu he) x hx hx0
  exact ⟨lam,hlam,v,hvn,hve,fun i ↦ hv (e i) (Submodule.subset_span (mem_range_self i)),hmax⟩

end
end Yau.Analysis

end OAI
