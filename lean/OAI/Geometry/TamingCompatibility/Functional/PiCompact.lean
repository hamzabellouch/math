import Mathlib

namespace OAI

noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian ENNReal
open scoped BigOperators
namespace TamingCompatibility.CompactPi
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} {F : ι → Type*}
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]

lemma pi_compact (f : ∀ i, E →L[ℝ] F i) (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  classical
  choose K hK hsub using (fun i => (hf i).image_closedBall_subset_compact 1)
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (ContinuousLinearMap.pi f).toLinearMap zero_lt_one).2
  refine ⟨{x | ∀ i, x i ∈ K i}, isCompact_pi_infinite hK, ?_⟩
  rintro _ ⟨x,hx,rfl⟩ i
  exact hsub i ⟨x,hx,rfl⟩

end TamingCompatibility.CompactPi

end

end OAI
