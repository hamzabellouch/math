import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapLinearCoordinates

namespace OAI

/-! A transverse linear coordinate for a regular curve in the surface plane. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def planeCurveLinear (v w : Base) : Base →L[ℝ] Base :=
  (ContinuousLinearMap.proj (0 : Fin 2)).smulRight v +
    (ContinuousLinearMap.proj (1 : Fin 2)).smulRight w

lemma planeCurveLinear_apply (v w x : Base) :
    planeCurveLinear v w x = x 0 • v+x 1 • w := rfl

theorem exists_plane_curve_frame {w : Base} (hw : w ≠ 0) :
    ∃ v : Base, Function.Bijective (planeCurveLinear v w) := by
  obtain ⟨v,hli⟩ := exists_linearIndependent_pair_of_one_lt_finrank
    (R := ℝ) (M := Base) (by simp [Base]) hw
  refine ⟨v,?_⟩
  have hz : ∀ x, planeCurveLinear v w x = 0 → x = 0 := by
    intro x hx
    have he : x 1 • w+x 0 • v = 0 := by
      rw [add_comm]
      exact hx
    obtain ⟨h1,h0⟩ := (LinearIndependent.pair_iff.mp hli) (x 1) (x 0) he
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hi : Function.Injective (planeCurveLinear v w) := by
    intro x y he
    apply sub_eq_zero.mp
    apply hz
    rw [map_sub,he,sub_self]
  exact ⟨hi,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (planeCurveLinear v w).toLinearMap) rfl).mp hi⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
