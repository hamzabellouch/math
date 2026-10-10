import OAI.MeasureTheory.Falconer.Angular.GnomonicChart
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.Normed.Module.Normalize

namespace OAI

/-! # Sending the prepared direction to the canonical north pole

An orthogonal reflection handles every equal-norm pair, including opposite
directions. Normalization and all cap distances commute with this fixed
linear isometry, so the original prepared cap can be transported exactly.
-/

namespace Falconer
open Set MeasureTheory NormedSpace

theorem exists_isometry_of_norm_eq {d : ℕ} (u v : Space d) (h : ‖u‖ = ‖v‖) :
    ∃ e : Space d ≃ₗᵢ[ℝ] Space d, e u = v :=
  ⟨(ℝ ∙ (u-v))ᗮ.reflection, Submodule.reflection_sub h⟩

theorem linearIsometryEquiv_normalize {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x : Space d) : normalize (e x) = e (normalize x) := by
  simp only [NormedSpace.normalize,e.norm_map,map_smul]

theorem linearIsometryEquiv_normalize_sub {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y : Space d) : normalize (e x-e y) = e (normalize (x-y)) := by
  rw [← map_sub,linearIsometryEquiv_normalize]

theorem linearIsometryEquiv_cap_norm {d : ℕ} (e : Space d ≃ₗᵢ[ℝ] Space d)
    (x y u : Space d) :
    ‖normalize (e x-e y)-e u‖ = ‖normalize (x-y)-u‖ := by
  rw [linearIsometryEquiv_normalize_sub,← map_sub,e.norm_map]

noncomputable def northRotation {n : ℕ} (u : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (ℝ ∙ ((u : Space (n+1))-(gnomonicChart (0 : Space n) : Space (n+1))))ᗮ.reflection

theorem northRotation_apply {n : ℕ} (u : Sphere (n+1)) :
    northRotation u u = (gnomonicChart (0 : Space n) : Space (n+1)) := by
  exact Submodule.reflection_sub (by rw [sphere_norm,sphere_norm])

theorem northRotation_sphereMap {n : ℕ} (u : Sphere (n+1)) :
    sphereMap (northRotation u) u = gnomonicChart (0 : Space n) := by
  apply Subtype.ext
  exact northRotation_apply u

theorem northRotation_normalize_sub {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    normalize (northRotation u x-northRotation u y) = northRotation u (normalize (x-y)) :=
  linearIsometryEquiv_normalize_sub (northRotation u) x y

theorem northRotation_cap_norm {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    ‖normalize (northRotation u x-northRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ =
      ‖normalize (x-y)-(u : Space (n+1))‖ := by
  rw [← northRotation_apply u]
  exact linearIsometryEquiv_cap_norm (northRotation u) x y u

theorem northRotation_cap_iff {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) (δ : ℝ) :
    ‖normalize (northRotation u x-northRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ ≤ δ ↔
      ‖normalize (x-y)-(u : Space (n+1))‖ ≤ δ := by
  rw [northRotation_cap_norm]

/-- Preparation uses the direction `y-x`; the inverse phase uses `x-y`. -/
noncomputable def reverseNorthRotation {n : ℕ} (u : Sphere (n+1)) :
    Space (n+1) ≃ₗᵢ[ℝ] Space (n+1) :=
  (LinearIsometryEquiv.neg ℝ).trans (northRotation u)

theorem reverseNorthRotation_apply {n : ℕ} (u : Sphere (n+1)) :
    reverseNorthRotation u (-(u : Space (n+1))) =
      (gnomonicChart (0 : Space n) : Space (n+1)) := by
  change northRotation u (-(-(u : Space (n+1)))) = _
  rw [neg_neg,northRotation_apply]

theorem reverseNorthRotation_cap_norm {n : ℕ} (u : Sphere (n+1)) (x y : Space (n+1)) :
    ‖normalize (reverseNorthRotation u x-reverseNorthRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ =
      ‖normalize (y-x)-(u : Space (n+1))‖ := by
  change ‖normalize (northRotation u (-x)-northRotation u (-y))-
    (gnomonicChart (0 : Space n) : Space (n+1))‖ = _
  rw [northRotation_cap_norm,show -x- -y = y-x by abel]

theorem reverseNorthRotation_cap_lt_iff {n : ℕ} (u : Sphere (n+1))
    (x y : Space (n+1)) (δ : ℝ) :
    ‖normalize (reverseNorthRotation u x-reverseNorthRotation u y)-
      (gnomonicChart (0 : Space n) : Space (n+1))‖ < δ ↔
      ‖normalize (y-x)-(u : Space (n+1))‖ < δ := by
  rw [reverseNorthRotation_cap_norm]

end Falconer

end OAI
