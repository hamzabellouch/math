import OAI.Probability.InvariantIsing.Cavity.CavityFrameOrbit
import Mathlib.Probability.Distributions.Gaussian.Fernique

namespace OAI

/-! Angular averaging for the moments of fresh Haar frame coordinates. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace InvariantIsing

lemma cavity_matrixRotation_mul_apply {n : ℕ} (U V : Orthogonal n)
    (x : EuclideanSpace ℝ (Fin n)) :
    matrixRotation (U * V) x = matrixRotation U (matrixRotation V x) := by
  ext i
  change (((U : Matrix (Fin n) (Fin n) ℝ) * (V : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x.ofLp) i =
    ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ ((V : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma cavity_unit_vector_transitive {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : Orthogonal n, matrixRotation U v = w := by
  have ho (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ = 1) :
      Orthonormal ℝ (fun _ : Fin 1 => x) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    simp [hij, hx]
  obtain ⟨U, hU⟩ := cavity_orthonormal_transitive _ _ (ho v hv) (ho w hw)
  exact ⟨cavityRotationMatrix U, (cavityRotationMatrix_apply U v).trans (hU 0)⟩

lemma continuous_cavityRotationAction (n : ℕ) :
    Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) => matrixRotation p.1 p.2) := by
  change Continuous (fun p : Orthogonal n × EuclideanSpace ℝ (Fin n) =>
    WithLp.toLp 2 ((p.1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ p.2.ofLp))
  exact (PiLp.continuous_toLp 2 _).comp
    ((continuous_subtype_val.comp continuous_fst).matrix_mulVec
      ((PiLp.continuous_ofLp 2 _).comp continuous_snd))

lemma cavity_sphere_average_independent {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u w : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ) =
      ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
  obtain ⟨V, hV⟩ := cavity_unit_vector_transitive u w hu hw
  rw [← hV]
  simp_rw [← cavity_matrixRotation_mul_apply]
  exact (integral_mul_right_eq_self (μ := μ)
    (fun U : Orthogonal n => |⟪v, matrixRotation U u⟫| ^ p) V).symm

theorem cavity_sphere_radial_average {n : ℕ}
    (μ : Measure (Orthogonal n)) [μ.IsMulRightInvariant]
    (v u x : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (p : ℕ) :
    (∫ U, |⟪v, matrixRotation U x⟫| ^ p ∂μ) =
      ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U u⟫| ^ p ∂μ := by
  by_cases hx : x = 0
  · subst x
    by_cases hp : p = 0 <;> simp [hp]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  let w := ‖x‖⁻¹ • x
  have hw : ‖w‖ = 1 := by simp [w, norm_smul, hn]
  have hxw : x = ‖x‖ • w := by simp [w, smul_smul, hn]
  calc
    _ = ‖x‖ ^ p * ∫ U, |⟪v, matrixRotation U w⟫| ^ p ∂μ := by
      conv_lhs => rw [hxw]
      simp_rw [map_smul, real_inner_smul_right, abs_mul, abs_norm, mul_pow]
      rw [integral_const_mul]
    _ = _ := by rw [cavity_sphere_average_independent μ v w u hw hu p]

end InvariantIsing

end

end OAI
