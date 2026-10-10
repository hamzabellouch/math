import Mathlib

namespace OAI

/-! Equality on the closed support of a smooth cutoff determines every
jet there, including at its boundary. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma iteratedFDeriv_eq_on_tsupport {χ : E → ℝ} (hχ : Continuous χ)
    {U : Set E} (hU : IsOpen U) (hK : tsupport χ ⊆ U)
    {f g : E → F} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (he : EqOn f g (tsupport χ)) (m : ℕ) :
    EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (tsupport χ) := by
  have hfc : ContinuousOn (iteratedFDeriv ℝ m f) U := by
    apply (hf.continuousOn_iteratedFDerivWithin (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hU hx).symm
  have hgc : ContinuousOn (iteratedFDeriv ℝ m g) U := by
    apply (hg.continuousOn_iteratedFDerivWithin (by simp) hU.uniqueDiffOn).congr
    intro x hx
    exact (iteratedFDerivWithin_of_isOpen m hU hx).symm
  have ho : EqOn (iteratedFDeriv ℝ m f) (iteratedFDeriv ℝ m g) (Function.support χ) := by
    intro x hx
    have hh : f =ᶠ[𝓝 x] g := by
      filter_upwards [hχ.isOpen_support.mem_nhds hx] with y hy
      exact he (subset_tsupport χ hy)
    exact (hh.iteratedFDeriv ℝ m).self_of_nhds
  exact ho.of_subset_closure (hfc.mono hK) (hgc.mono hK) subset_closure Subset.rfl

end ClosedSurfaceR4

end

end OAI
