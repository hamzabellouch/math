import OAI.MeasureTheory.Falconer.Geometry.ChartCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace OAI

/-!
# Choosing a frame adapted to a failed perpendicular test

Two Householder reflections map a fixed orthonormal pair to a prescribed
one. This places the nonstationary tangent direction in the first chart
coordinate without any loss depending on the cap center.
-/

namespace Falconer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem orthonormal_pair_isometry {a b w t : E}
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : inner ℝ a b = 0)
    (hw : ‖w‖ = 1) (ht : ‖t‖ = 1) (hwt : inner ℝ w t = 0) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e a = w ∧ e b = t := by
  let e₁ := (ℝ ∙ (a-w))ᗮ.reflection
  have h₁ : e₁ a = w := Submodule.reflection_sub (ha.trans hw.symm)
  have horth : inner ℝ w (e₁ b) = 0 := by
    rw [← h₁,e₁.inner_map_map]
    exact hab
  let e₂ := (ℝ ∙ (e₁ b-t))ᗮ.reflection
  have h₂ : e₂ (e₁ b) = t :=
    Submodule.reflection_sub ((e₁.norm_map b).trans (hb.trans ht.symm))
  have hfix : e₂ w = w := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left,inner_sub_right,horth,hwt]
    ring
  exact ⟨e₁.trans e₂,by simpa only [LinearIsometryEquiv.trans_apply,h₁] using hfix,h₂⟩

theorem exists_adapted_chart_frame {n : ℕ} {w t : Space (n+2)}
    (hw : ‖w‖ = 1) (ht : ‖t‖ = 1) (hwt : inner ℝ w t = 0) :
    ∃ e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2), e (chartPole n) = w ∧ e (chartAxis n) = t :=
  orthonormal_pair_isometry (chartPole_norm n) (chartAxis_norm n)
    (chartPole_inner_axis n) hw ht hwt

theorem inner_isometry_pullback (e : E ≃ₗᵢ[ℝ] E) (x v : E) :
    inner ℝ (e x) v = inner ℝ x (e.symm v) := by
  rw [← e.inner_map_map x (e.symm v),e.apply_symm_apply]

theorem normalizedLine_isometry (e : E ≃ₗᵢ[ℝ] E) (a t : E) (u : ℝ) :
    normalizedLine (e a) (e t) u = e (normalizedLine a t u) := by
  simp only [normalizedLine,← e.map_smul,← e.map_add,e.norm_map]

end Falconer

end OAI
