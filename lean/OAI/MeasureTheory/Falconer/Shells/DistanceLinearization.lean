import OAI.MeasureTheory.Falconer.Geometry.DyadicCube
import Mathlib.Analysis.InnerProductSpace.Basic

namespace OAI

/-! # The actual distance Taylor error for the suffix reduction

The error estimate is dimension independent before insertion of the cube
diameter. Its proof is the exact squared-norm identity, so no differentiable
extension across the diagonal is needed.
-/

namespace Falconer
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_linearization_bounds (u v : E) (hu : 0 < ‖u‖) :
    0 ≤ ‖v‖-inner ℝ (‖u‖⁻¹ • u) v ∧
      ‖v‖-inner ℝ (‖u‖⁻¹ • u) v ≤ ‖v-u‖^2/(2*‖u‖) := by
  have hi : inner ℝ (‖u‖⁻¹ • u) v = inner ℝ u v/‖u‖ := by
    rw [real_inner_smul_left]
    ring
  rw [hi]
  have hb : inner ℝ u v/‖u‖ ≤ ‖v‖ := by
    apply (div_le_iff₀ hu).mpr
    exact (real_inner_le_norm u v).trans_eq (mul_comm _ _)
  have he : 2*‖u‖*(‖v‖-inner ℝ u v/‖u‖) =
      ‖v-u‖^2-(‖v‖-‖u‖)^2 := by
    have hs := norm_sub_sq_real v u
    rw [real_inner_comm u v] at hs
    field_simp
    nlinarith
  refine ⟨sub_nonneg.mpr hb,?_⟩
  apply (le_div_iff₀ (mul_pos (by norm_num) hu)).mpr
  nlinarith [sq_nonneg (‖v‖-‖u‖)]

theorem norm_linearization_abs_le (u v : E) (hu : 0 < ‖u‖) :
    |‖v‖-inner ℝ (‖u‖⁻¹ • u) v| ≤ ‖v-u‖^2/(2*‖u‖) := by
  rw [abs_of_nonneg (norm_linearization_bounds u v hu).1]
  exact (norm_linearization_bounds u v hu).2

omit [InnerProductSpace ℝ E] in
theorem pair_displacement_bound (x y c₁ c₂ : E) {δ₁ δ₂ : ℝ}
    (h₁ : ‖x-c₁‖ ≤ δ₁) (h₂ : ‖y-c₂‖ ≤ δ₂) :
    ‖(x-y)-(c₁-c₂)‖ ≤ δ₁+δ₂ := by
  have he : (x-y)-(c₁-c₂) = (x-c₁)-(y-c₂) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add h₁ h₂)

/-- Original distances on a pair of small cubes have the required
quadratic error relative to their center direction. -/
theorem DyadicCube.distance_linearization {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    |dist x y-inner ℝ (‖P.center-Q.center‖⁻¹ • (P.center-Q.center)) (x-y)| ≤
      2*(d:ℝ)*P.side^2/g := by
  have hQp : 0 < Q.side := by rw [hQ]; exact hP
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
    rw [hQ] at h₂
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hsquare : ‖(x-y)-(P.center-Q.center)‖^2 ≤ 4*(d:ℝ)*P.side^2 := by
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hδ
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]
  have hnorm : 0 < ‖P.center-Q.center‖ := hg.trans_le hsep
  rw [dist_eq_norm]
  apply (norm_linearization_abs_le _ _ hnorm).trans
  calc
    _ ≤ (4*(d:ℝ)*P.side^2)/(2*‖P.center-Q.center‖) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    _ ≤ (4*(d:ℝ)*P.side^2)/(2*g) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hsep (by norm_num))
    _ = _ := by ring

end Falconer

end OAI
