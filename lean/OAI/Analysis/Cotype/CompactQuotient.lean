import OAI.Analysis.Cotype.WeightedCompact
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

instance kernelClosed (j : H →L[ℝ] X) : IsClosed (j.ker : Set H) := j.isClosed_ker

abbrev KernelQuotient (j : H →L[ℝ] X) : Type _ := H ⧸ j.ker

def quotientFactor (j : H →L[ℝ] X) : KernelQuotient j →L[ℝ] X :=
  j.ker.liftQL j le_rfl

@[simp] theorem quotientFactor_mk (j : H →L[ℝ] X) (z : H) :
    quotientFactor j (j.ker.mkQL z) = j z := rfl

theorem quotientFactor_injective (j : H →L[ℝ] X) : Function.Injective (quotientFactor j) := by
  apply (quotientFactor j).ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  obtain ⟨z,rfl⟩ := j.ker.mkQ_surjective g
  change j z = 0 at hg
  change j.ker.mkQ z ∈ (⊥ : Submodule ℝ (KernelQuotient j))
  change (Submodule.Quotient.mk z : KernelQuotient j) = 0
  exact (Submodule.Quotient.mk_eq_zero j.ker).mpr hg

theorem quotient_representative_two (j : H →L[ℝ] X) (g : KernelQuotient j) :
    ∃ z : H, j.ker.mkQL z = g ∧ ‖z‖ ≤ 2 * ‖g‖ := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], by simp [hg]⟩
  · obtain ⟨z,hz,hn⟩ := Submodule.Quotient.norm_mk_lt g (norm_pos_iff.mpr hg)
    exact ⟨z,hz, by linarith⟩

theorem quotientFactor_norm (j : H →L[ℝ] X) : ‖quotientFactor j‖ ≤ ‖j‖ := by
  apply (quotientFactor j).opNorm_le_bound (norm_nonneg _)
  intro g
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε / (‖j‖ + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨z,hz,hn⟩ := Submodule.Quotient.norm_mk_lt g hδ
  have he : ‖j‖ * δ ≤ ε := by
    have hh : δ * (‖j‖ + 1) = ε := by dsimp [δ]; field_simp
    nlinarith [norm_nonneg j]
  have h : ‖quotientFactor j g‖ ≤ ‖j‖ * ‖z‖ := by
    rw [← hz]
    exact j.le_opNorm z
  nlinarith [mul_le_mul_of_nonneg_left hn.le (norm_nonneg j)]

theorem quotientFactor_compact (j : H →L[ℝ] X) (hj : IsCompactOperator j) :
    IsCompactOperator (quotientFactor j) := by
  obtain ⟨K,hK,hjK⟩ := hj.image_closedBall_subset_compact (f := j.toLinearMap) 2
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (quotientFactor j).toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
  refine ⟨K,hK,?_⟩
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨z,hz,hn⟩ := quotient_representative_two j g
  apply hjK
  refine ⟨z,?_,?_⟩
  · have hg' : ‖g‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hg
    simpa [Metric.mem_closedBall, dist_zero_right] using hn.trans (by linarith : 2*‖g‖ ≤ 2)
  · rw [← hz]
    rfl

variable [CompleteSpace X] (A : ℕ → Submodule ℝ X)

def compactInclusion : A 0 →L[ℝ] KernelQuotient (weightedMap A) :=
  (weightedMap A).ker.mkQL.comp (lp.singleContinuousLinearMap ℝ (fun l => A l) 2 0)

omit [CompleteSpace X] in
theorem compactInclusion_norm : ‖compactInclusion A‖ ≤ 1 := by
  apply (compactInclusion A).opNorm_le_bound zero_le_one
  intro x
  change ‖(Submodule.Quotient.mk (lp.single 2 0 x) : KernelQuotient (weightedMap A))‖ ≤ 1 * ‖x‖
  simpa only [lp.norm_single (by norm_num : (0 : ENNReal) < 2), one_mul] using
    Submodule.Quotient.norm_mk_le (weightedMap A).ker (lp.single 2 0 x)

theorem quotientFactor_compactInclusion (x : A 0) :
    quotientFactor (weightedMap A) (compactInclusion A x) = (x : X) :=
  weightedMap_single_zero A x

end Cotype

end

end OAI
