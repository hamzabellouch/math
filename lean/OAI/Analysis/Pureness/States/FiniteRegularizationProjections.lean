import OAI.Analysis.Pureness.States.FiniteRegularizationContinuity
import OAI.Analysis.Pureness.Cuntz.CuntzRescaling
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped NNReal ENNReal
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_projection_cut {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (p : Positive D) (hp : IsIdempotentElem p.1)
    (ε : ℝ≥0) (hε : ε < 1) : (Positive.cut ε p).1 = (1-(ε : ℝ)) • p.1 := by
  change cfcₙ (fun t : ℝ => max (t-ε) 0) p.1 = _
  rw [← cfcₙ_const_mul_id (1-(ε : ℝ)) p.1]
  apply cfcₙ_congr
  intro t ht
  have hs : t = 0 ∨ t = 1 := by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hp.quasispectrum_subset ℝ ht
  rcases hs with rfl | rfl
  · simp
  · simp only [mul_one, max_eq_left (sub_nonneg.mpr (le_of_lt (show (ε : ℝ) < 1 from hε)))]

lemma finiteProjection_cut_class (n : ℕ) (p : Positive (FinMatrix A n))
    (hp : IsIdempotentElem p.1) (ε : ℝ≥0) (hε : ε < 1) :
    finitePositiveClass n (Positive.cut ε p) = finitePositiveClass n p := by
  have h := positive_smul_cuntz_equiv p.1 (1-(ε : ℝ)) (sub_pos.mpr hε)
  apply le_antisymm
  · apply (finitePositiveClass_le_iff n _ _).mpr
    rw [positive_projection_cut p hp ε hε]
    exact h.1
  · apply (finitePositiveClass_le_iff n _ _).mpr
    rw [positive_projection_cut p hp ε hε]
    exact h.2

theorem regularizedFiniteDimension_projection
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (p : Positive (FinMatrix A n)) (hp : IsIdempotentElem p.1) :
    regularizedFiniteDimension d hd (finitePositiveClass n p) = d (finitePositiveClass n p) := by
  apply le_antisymm (regularizedFiniteDimension_le d hd _)
  rw [regularizedFiniteDimension_eval]
  have h := cut_class_value_le_regularized d n p (1/2) (by norm_num)
  rwa [finiteProjection_cut_class n p hp (1/2) (by norm_num)] at h

def regularizedProjectionState (n : ℕ) (p : Positive (FinMatrix A n))
    (hp : IsIdempotentElem p.1) (f : OrderedSemigroup.StateSpace (finitePositiveClass n p)) :
    OrderedSemigroup.StateSpace (finitePositiveClass n p) := by
  let d := regularizedFiniteDimension f.toAddHom f.monotone
  refine ⟨d, d.map_zero, d.map_add, regularizedFiniteDimension_monotone f.toAddHom f.monotone, ?_⟩
  change regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass n p) = 1
  rw [regularizedFiniteDimension_projection f.toAddHom f.monotone n p hp]
  exact f.at_unit
end CuntzPureness

end

end OAI
