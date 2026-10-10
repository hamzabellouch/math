import OAI.Probability.SwitchChain.PairEqualitySlice
import OAI.Probability.SwitchChain.PairEqualityLocalization

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.PairEquality
open PairResampling PairFiber
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

abbrev AssignmentSpace (G : GraphState n d) (i j : Fin n) :=
  EuclideanSpace ℝ (Assignment G.val i j)

def assignmentRestriction (G : GraphState n d) (i j : Fin n) (hij : i ≠ j) :
    StateSpace n d →ₗ[ℝ] AssignmentSpace G i j where
  toFun f := WithLp.toLp 2 (fun T => f ((stateFiberEquiv G i j hij).symm T).val)
  map_add' _ _ := by ext T; rfl
  map_smul' _ _ := by ext T; rfl

@[simp] theorem assignmentRestriction_apply (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : StateSpace n d) (T : Assignment G.val i j) :
    assignmentRestriction G i j hij f T = f ((stateFiberEquiv G i j hij).symm T).val := rfl

private theorem sum_assignment_reconstruct (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f : GraphState n d → ℝ) :
    (∑ T : Assignment G.val i j, f ((stateFiberEquiv G i j hij).symm T).val) =
      ∑ H ∈ fiberStates {i,j} G, f H := by
  calc
    _ = ∑ H : ↥(fiberStates {i,j} G), f H.val :=
      (resamplingFiberEquiv G i j hij).symm.sum_comp (fun H => f H.val)
    _ = _ := Finset.sum_coe_sort _ f

theorem assignmentRestriction_inner_supported (G : GraphState n d) (i j : Fin n)
    (hij : i ≠ j) (f z : StateSpace n d)
    (hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0) :
    ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ⟪f,z⟫ := by
  rw [state_inner]
  have hinner : ⟪assignmentRestriction G i j hij f, assignmentRestriction G i j hij z⟫ =
      ∑ T : Assignment G.val i j,
        f ((stateFiberEquiv G i j hij).symm T).val *
          z ((stateFiberEquiv G i j hij).symm T).val := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  rw [hinner, sum_assignment_reconstruct G i j hij (fun H => f H * z H)]
  unfold fiberStates
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro H hH
  by_cases h : SameFiber {i,j} G.val H.val
  · simp only [ite_eq_left h]
  · simp [h, hz H h]

def assignmentVector (G : GraphState n d) (i j k l : Fin n) : AssignmentSpace G i j :=
  WithLp.toLp 2 (fun T => if active i j k l G then
    SliceMoments.centeredEqual (singletonSet G.val i j) (leftSet G.val i j).card
      k l T.val else 0)

theorem restriction_localizedVector (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) :
    assignmentRestriction G i j hij (localizedVector i j k l G) =
      assignmentVector G i j k l := by
  ext T
  rw [assignmentRestriction_apply]
  have h := reconstructed_sameFiber G i j hij T
  have ha := active_sameFiber i j k l hij h
  change (if SameFiber {i,j} G.val ((stateFiberEquiv G i j hij).symm T).val.val then
    (if active i j k l ((stateFiberEquiv G i j hij).symm T).val then
      centered i j k l ((stateFiberEquiv G i j hij).symm T).val else 0) else 0) = _
  rw [ite_eq_left h, ← ha]
  by_cases hA : active i j k l G
  · simpa only [assignmentVector, WithLp.toLp_ofLp, ite_eq_left hA] using
      centered_reconstruction G i j k l hij hkl hA T
  · simp [assignmentVector, hA]

theorem assignmentRestriction_projection (G : GraphState n d) (i j k l : Fin n)
    (hij : i ≠ j) (hkl : k ≠ l) (f : StateSpace n d) :
    assignmentRestriction G i j hij (projection i j k l f) =
      (Submodule.span ℝ {assignmentVector G i j k l}).starProjection
        (assignmentRestriction G i j hij f) := by
  let z := localizedVector i j k l G
  have hz : ∀ H : GraphState n d, ¬ SameFiber {i,j} G.val H.val → z H = 0 := by
    intro H hH
    simp [z, localizedVector, restrictCell, hH]
  have hlocal := projection_localization i j k l hij G f
  have hrestrict := congrArg (assignmentRestriction G i j hij) hlocal
  have hcell : assignmentRestriction G i j hij
      (restrictCell (fun H => SameFiber {i,j} G.val H.val) (projection i j k l f)) =
      assignmentRestriction G i j hij (projection i j k l f) := by
    ext T
    simp only [assignmentRestriction_apply, restrictCell_apply,
      ite_eq_left (reconstructed_sameFiber G i j hij T)]
  rw [hcell] at hrestrict
  rw [← hrestrict, Submodule.starProjection_singleton, map_smul,
    restriction_localizedVector G i j k l hij hkl, Submodule.starProjection_singleton]
  congr 1
  have hi := assignmentRestriction_inner_supported G i j hij f z hz
  have hn := assignmentRestriction_inner_supported G i j hij z z hz
  rw [restriction_localizedVector G i j k l hij hkl] at hi hn
  rw [real_inner_comm] at hi
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hn
  rw [hi, hn]
  congr 1
  exact real_inner_comm _ _

end Problem315.PairEquality

end

end OAI
