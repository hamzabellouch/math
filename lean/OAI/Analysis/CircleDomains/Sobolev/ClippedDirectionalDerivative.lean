import OAI.Analysis.CircleDomains.Sobolev.ClippedScalarEnergy

namespace OAI

/-! Clipped smooth functions have consistent ordinary directional
partials, including at the two clipping levels. -/
open Set Function Filter
open scoped Topology
namespace CircleDomainRigidity

 theorem fderiv_clipScalar_eq_ite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {z : E} (hu : ContinuousAt u z) :
    fderiv ℝ (clipScalar ∘ u) z = if u z ∈ Ioo 0 1 then fderiv ℝ u z else 0 := by
  by_cases hz : u z ∈ Ioo 0 1
  · simp only [hz, ↓reduceIte]
    apply EventuallyEq.fderiv_eq
    filter_upwards [hu.tendsto (isOpen_Ioo.mem_nhds hz)] with y hy
    exact clipScalar_eq ⟨hy.1.le, hy.2.le⟩
  · simp only [hz, ↓reduceIte]
    by_cases h0 : u z ≤ 0
    · apply IsLocalMin.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u z) ≤ clipScalar (u y)
        rw [clipScalar_of_nonpos h0]
        exact (clipScalar_mem _).1
    · have h1 : 1 ≤ u z := by
        have : ¬ u z < 1 := fun h => hz ⟨lt_of_not_ge h0, h⟩
        exact le_of_not_gt this
      apply IsLocalMax.fderiv_eq_zero
      exact Eventually.of_forall fun y => by
        change clipScalar (u y) ≤ clipScalar (u z)
        rw [clipScalar_of_one_le h1]
        exact (clipScalar_mem _).2

 theorem deriv_clipScalar_comp_curve {u : ℂ → ℝ} {γ : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hu : DifferentiableAt ℝ u (γ x)) (hγ : HasDerivAt γ v x) :
    deriv ((clipScalar ∘ u) ∘ γ) x = fderiv ℝ (clipScalar ∘ u) (γ x) v := by
  have hc : ContinuousAt (u ∘ γ) x := hu.continuousAt.comp hγ.continuousAt
  change fderiv ℝ (clipScalar ∘ (u ∘ γ)) x 1 = _
  rw [fderiv_clipScalar_eq_ite hc, fderiv_clipScalar_eq_ite hu.continuousAt]
  simp only [comp_apply]
  split_ifs with h
  · exact (hu.hasFDerivAt.comp_hasDerivAt x hγ).deriv
  · simp

 theorem deriv_eq_fderiv_of_eventuallyEq_clip
    {F u : ℂ → ℝ} {γ : ℝ → ℂ} {x : ℝ} {v : ℂ}
    (hF : F =ᶠ[𝓝 (γ x)] clipScalar ∘ u)
    (hu : DifferentiableAt ℝ u (γ x)) (hγ : HasDerivAt γ v x) :
    deriv (F ∘ γ) x = fderiv ℝ F (γ x) v := by
  rw [(hF.comp_tendsto hγ.continuousAt.tendsto).deriv_eq, hF.fderiv_eq]
  exact deriv_clipScalar_comp_curve hu hγ

end CircleDomainRigidity

end OAI
