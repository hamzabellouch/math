import OAI.GroupTheory.PolycyclicRecognition.Algebra.EigenlineConeEstimates

namespace OAI

/-! # Nonzero eigenline cones and separation

Explicit functional inequalities separate cones around different lines and
bound their distance from a repelling hyperplane. These are the geometric
conditions used by the contracting ping-pong argument.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def eigenlineCone (φ : V →L[ℝ] ℝ) (v : V) (ε : ℝ) : Set V :=
  {x | x ≠ 0 ∧ ‖eigenlineRemainder φ v x‖ ≤ ε * |φ x|}

theorem eigenlineCone_functional_ne_zero (φ : V →L[ℝ] ℝ) (v : V) (ε : ℝ)
    {x : V} (hx : x ∈ eigenlineCone φ v ε) : φ x ≠ 0 := by
  intro hz
  have hnorm : ‖x‖ ≤ 0 := by simpa [eigenlineRemainder, hz] using hx.2
  exact hx.1 (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

theorem eigenline_cone_functional_upper (ψ θ : V →L[ℝ] ℝ) (w x : V) (ε : ℝ)
    (hx : ‖eigenlineRemainder ψ w x‖ ≤ ε * |ψ x|) :
    |θ x| ≤ (|θ w| + ‖θ‖ * ε) * |ψ x| := by
  have he : θ x = θ (eigenlineRemainder ψ w x) + ψ x * θ w := by
    simp [eigenlineRemainder]
  calc
    |θ x| = |θ (eigenlineRemainder ψ w x) + ψ x * θ w| := congrArg abs he
    _ ≤ |θ (eigenlineRemainder ψ w x)| + |ψ x * θ w| := abs_add_le _ _
    _ ≤ ‖θ‖ * ‖eigenlineRemainder ψ w x‖ + |ψ x| * |θ w| := by
      exact add_le_add (by simpa only [Real.norm_eq_abs] using (θ.le_opNorm
        (eigenlineRemainder ψ w x))) (le_of_eq (abs_mul _ _))
    _ ≤ ‖θ‖ * (ε * |ψ x|) + |ψ x| * |θ w| := by
      gcongr
    _ = _ := by ring

theorem eigenline_cone_transverse_nonzero (ψ θ : V →L[ℝ] ℝ) (w : V) (ε : ℝ)
    (hgap : ‖θ‖ * ε < |θ w|) {x : V} (hx : x ∈ eigenlineCone ψ w ε) : θ x ≠ 0 := by
  have hp : 0 < (|θ w| - ‖θ‖ * ε) * |ψ x| :=
    mul_pos (sub_pos.mpr hgap) (abs_pos.mpr (eigenlineCone_functional_ne_zero ψ w ε hx))
  have hl := eigenline_cone_functional_lower ψ θ w x ε hx.2
  exact abs_pos.mp (lt_of_lt_of_le hp hl)

theorem eigenline_cones_disjoint_of_separator
    (φ ψ θ : V →L[ℝ] ℝ) (v w : V) (ε : ℝ) (hθv : θ v = 0)
    (hsep : (‖θ‖ * ε) * (|φ w| + ‖φ‖ * ε) < |θ w| - ‖θ‖ * ε) :
    Disjoint (eigenlineCone φ v ε) (eigenlineCone ψ w ε) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hθ := eigenline_cone_functional_upper φ θ v x ε hx.2
  rw [hθv, abs_zero, zero_add] at hθ
  have hφ := eigenline_cone_functional_upper ψ φ w x ε hy.2
  have hl := eigenline_cone_functional_lower ψ θ w x ε hy.2
  have hpos : 0 < |ψ x| := abs_pos.mpr (eigenlineCone_functional_ne_zero ψ w ε hy)
  have hε : 0 ≤ ε := by
    have hfx : 0 < |φ x| := abs_pos.mpr (eigenlineCone_functional_ne_zero φ v ε hx)
    have := (norm_nonneg (eigenlineRemainder φ v x)).trans hx.2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hφ (mul_nonneg (norm_nonneg θ) hε)
  have hstrict := mul_lt_mul_of_pos_right hsep hpos
  nlinarith

end PolycyclicRecognition

end

end OAI
