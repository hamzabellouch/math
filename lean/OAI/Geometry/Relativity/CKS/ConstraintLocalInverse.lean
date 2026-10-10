import OAI.Geometry.Relativity.CKS.ConstraintDensityDefinitions

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace CKSIntrinsicConstraints
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
theorem exists_smooth_local_inverse {f : E → E} {x : E}
    (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ f y)
    (hb : Function.Bijective (fderiv ℝ f x)) :
    ∃ e : OpenPartialHomeomorph E E, (e : E → E) = f ∧ x ∈ e.source ∧
      (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ e y) ∧
      (∀ᶠ y in 𝓝 (f x), ContDiffAt ℝ ∞ e.symm y) := by
  let L : E ≃L[ℝ] E := (LinearEquiv.ofBijective (fderiv ℝ f x).toLinearMap hb).toContinuousLinearEquiv
  have hLeq : L.toContinuousLinearMap = fderiv ℝ f x := by ext v; rfl
  have hd : HasFDerivAt f (L : E →L[ℝ] E) x := by
    rw [hLeq]
    exact (hf.self_of_nhds.differentiableAt (by simp)).hasFDerivAt
  let e := hf.self_of_nhds.toOpenPartialHomeomorph f hd (by simp)
  have hx : x ∈ e.source := hf.self_of_nhds.mem_toOpenPartialHomeomorph_source hd (by simp)
  refine ⟨e,rfl,hx,hf,?_⟩
  have hL : ∀ᶠ y in 𝓝 x, ∃ L' : E ≃L[ℝ] E,
      L'.toContinuousLinearMap = fderiv ℝ f y :=
    by
    have h := (hf.self_of_nhds.continuousAt_fderiv (by simp)).eventually (hLeq ▸ L.nhds)
    exact h
  have hec : Tendsto e.symm (𝓝 (f x)) (𝓝 x) := e.tendsto_symm hx
  filter_upwards [e.open_target.mem_nhds (e.map_source hx),hec.eventually hf,
    hec.eventually hL] with y hy hfy hLy
  obtain ⟨L',hL'⟩ := hLy
  apply e.contDiffAt_symm hy (f₀' := L') _ hfy
  rw [hL']
  exact (hfy.differentiableAt (by simp)).hasFDerivAt
end CKSIntrinsicConstraints

end

end OAI
