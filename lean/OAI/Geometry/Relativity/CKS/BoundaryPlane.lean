import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Set Metric Module
open scoped ENNReal
namespace CKSIntrinsicGeometry
abbrev E3 := EuclideanSpace ℝ (Fin 3)
def boundaryPlane : Submodule ℝ E3 :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).toLinearMap.ker

lemma boundaryPlane_finrank : Module.finrank ℝ boundaryPlane = 2 := by
  let f : E3 →ₗ[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).toLinearMap
  have hsurj : Function.Surjective f := by
    intro t
    exact ⟨EuclideanSpace.single 0 t, by simp [f]⟩
  have h := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    finrank_euclideanSpace_fin] at h
  change Module.finrank ℝ f.ker = 2
  omega

lemma boundary_plane_ball_area_finite (a : E3) (r : ℝ) :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure E3)
      (ball a r ∩ {x : E3 | x 0 = 0}) < ⊤ := by
  let S : Set boundaryPlane := {x | (x : E3) ∈ ball a r}
  have heq : (ball a r ∩ {x : E3 | x 0 = 0}) =
      ((↑) : boundaryPlane → E3) '' S := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.property⟩
  rw [heq]
  have hiso : Isometry ((↑) : boundaryPlane → E3) := fun _ _ => rfl
  rw [hiso.hausdorffMeasure_image (Or.inl (by norm_num))]
  have hS : Bornology.IsBounded S := by
    apply (isBounded_ball (x := (0 : boundaryPlane)) (r := r + ‖a‖)).subset
    intro x hx
    change dist x 0 < r + ‖a‖
    rw [dist_zero_right]
    change ‖(x : E3)‖ < r + ‖a‖
    calc ‖(x : E3)‖ = ‖((x : E3) - a) + a‖ := by congr 1; abel
         _ ≤ ‖(x : E3) - a‖ + ‖a‖ := norm_add_le _ _
         _ < r + ‖a‖ := by
           have hxr : ‖(x : E3) - a‖ < r := by simpa [S, mem_ball, dist_eq_norm] using hx
           linarith
  have hfin : (Measure.hausdorffMeasure (Module.finrank ℝ boundaryPlane : ℝ) :
      Measure boundaryPlane) S < ⊤ := hS.measure_lt_top
  simpa only [boundaryPlane_finrank, Nat.cast_ofNat] using hfin

end CKSIntrinsicGeometry

end

end OAI
