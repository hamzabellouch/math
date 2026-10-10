import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma scalar_of_commutes_rankOne (Z : H →L[ℂ] H)
    (hz : ∀ x y : H,Commute Z (InnerProductSpace.rankOne ℂ x y)) :
    ∃ c : ℂ,Z=c • (1:H →L[ℂ] H) := by
  rcases subsingleton_or_nontrivial H with hH|hH
  · let := hH
    exact ⟨0,Subsingleton.elim _ _⟩
  · let := hH
    obtain ⟨e,he⟩ := exists_ne (0:H)
    have hee : inner ℂ e e≠0 := inner_self_ne_zero.mpr he
    refine ⟨((inner ℂ e e)⁻¹*inner ℂ e (Z e)),?_⟩
    apply ContinuousLinearMap.ext
    intro x
    have hc := congrArg (fun A : H →L[ℂ] H => A e) (hz x e).eq
    change Z (inner ℂ e e • x)=inner ℂ e (Z e) • x at hc
    rw [map_smul] at hc
    have hc' := congrArg (fun y : H => (inner ℂ e e)⁻¹ • y) hc
    simpa only [smul_smul,inv_mul_cancel₀ hee,one_smul,
      smul_apply,one_apply_eq_self] using hc'

omit [CompleteSpace H] in
lemma scalar_of_dense_rankOne_tests (v : ℕ → H) (hv : DenseRange v)
    (Z : H →L[ℂ] H)
    (hz : ∀ i j,Commute Z (InnerProductSpace.rankOne ℂ (v i) (v j))) :
    ∃ c : ℂ,Z=c • (1:H →L[ℂ] H) := by
  have ht (i j : ℕ) (e : H) :
      inner ℂ (v j) e • Z (v i)=inner ℂ (v j) (Z e) • v i := by
    have h := congrArg (fun A : H →L[ℂ] H => A e) (hz i j).eq
    change Z (inner ℂ (v j) e • v i)=inner ℂ (v j) (Z e) • v i at h
    simpa only [map_smul] using h
  have hy (i : ℕ) (y e : H) :
      inner ℂ y e • Z (v i)=inner ℂ y (Z e) • v i := by
    exact hv.induction_on y
      (isClosed_eq ((continuous_id.inner continuous_const).smul continuous_const)
        ((continuous_id.inner continuous_const).smul continuous_const))
      (fun j => ht i j e)
  have hx (x y e : H) : inner ℂ y e • Z x=inner ℂ y (Z e) • x := by
    exact hv.induction_on x
      (isClosed_eq (continuous_const.smul Z.continuous)
        (continuous_const.smul continuous_id)) (fun i => hy i y e)
  apply scalar_of_commutes_rankOne Z
  intro x y
  change Z*InnerProductSpace.rankOne ℂ x y=InnerProductSpace.rankOne ℂ x y*Z
  apply ContinuousLinearMap.ext
  intro e
  change Z (inner ℂ y e • x)=inner ℂ y (Z e) • x
  rw [map_smul]
  exact hx x y e

end Kadison

end

end
end

end OAI
