import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace

namespace OAI
noncomputable section
namespace CuntzPureness
local instance finiteCoordinateReconstructionDecidableEq {X : Type*} :
    DecidableEq X := Classical.decEq X
variable {A E G : Type*}
variable [NormedAddCommGroup A] [NormedSpace ℂ A]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]

def finiteCoordinateReconstruction (L : G → A →L[ℂ] E) (R : G → E →L[ℂ] A)
    (s : Finset G) (c : G → ℂ) : E →L[ℂ] E :=
  ∑ g ∈ s, (L g).comp (c g • R g)

lemma finiteCoordinateReconstruction_apply (L : G → A →L[ℂ] E) (R : G → E →L[ℂ] A)
    (s : Finset G) (c : G → ℂ) (x : E) :
    finiteCoordinateReconstruction L R s c x = ∑ g ∈ s, L g (c g • R g x) := by
  simp only [finiteCoordinateReconstruction, sum_apply, ContinuousLinearMap.comp_apply, smul_apply]

lemma finiteCoordinateReconstruction_generator (L : G → A →L[ℂ] E) (R : G → E →L[ℂ] A)
    (hRL : ∀ g h a, R g (L h a) = if g = h then a else 0)
    (s : Finset G) (c : G → ℂ) (a : A) (g : G) :
    finiteCoordinateReconstruction L R s c (L g a) = (if g ∈ s then c g else 0) • L g a := by
  simp only [finiteCoordinateReconstruction_apply, hRL]
  by_cases hg : g ∈ s
  · rw [ite_eq_left hg, Finset.sum_eq_single g]
    · simp only [ite_true, map_smul]
    · intro b hb hbg
      simp only [ite_eq_right hbg, smul_zero, map_zero]
    · exact fun h => (h hg).elim
  · rw [ite_eq_right hg, zero_smul]
    apply Finset.sum_eq_zero
    intro b hb
    have hbg : b ≠ g := fun h => hg (h ▸ hb)
    simp only [ite_eq_right hbg, smul_zero, map_zero]

lemma finiteCoordinateReconstruction_norm_le (L : G → A →L[ℂ] E) (R : G → E →L[ℂ] A)
    (hL : ∀ g a, ‖L g a‖ ≤ ‖a‖) (hR : ∀ g x, ‖R g x‖ ≤ ‖x‖)
    (s : Finset G) (c : G → ℂ) (x : E) :
    ‖finiteCoordinateReconstruction L R s c x‖ ≤ (∑ g ∈ s, ‖c g‖) * ‖x‖ := by
  rw [finiteCoordinateReconstruction_apply, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro g hg
  apply (hL g _).trans
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hR g x) (norm_nonneg _)
end CuntzPureness

end

end OAI
