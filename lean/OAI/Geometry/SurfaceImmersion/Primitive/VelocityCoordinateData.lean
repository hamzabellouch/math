import OAI.Geometry.SurfaceImmersion.Primitive.VelocityPlaneBasis

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dot_smoothOn {f g : E → Vec} {U : Set E}
    (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (fun x => f x ⬝ᵥ g x) U :=
  ContDiffOn.sum (fun i _ => (contDiffOn_pi.mp hf i).mul (contDiffOn_pi.mp hg i))

lemma plane_coordinates_smoothOn {v e₁ e₂ : E → Vec} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (h₁ : ContDiffOn ℝ ∞ e₁ U)
    (h₂ : ContDiffOn ℝ ∞ e₂ U) :
    ContDiffOn ℝ ∞ (fun x => planeCoordinates (e₁ x) (e₂ x) (v x)) U := by
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact dot_smoothOn hv h₁
  · exact dot_smoothOn hv h₂

lemma norm_smul_normalize {v : Vec} (hv : v ≠ 0) :
    Real.sqrt (v ⬝ᵥ v) • normalize v = v := by
  simp [normalize, smul_smul, (Real.sqrt_pos.mpr (dot_self_pos hv)).ne']

lemma dot_normalize_self {v : Vec} (hv : v ≠ 0) :
    v ⬝ᵥ normalize v = Real.sqrt (v ⬝ᵥ v) := by
  have hp := dot_self_pos hv
  have hn := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, dotProduct_smul, smul_eq_mul]
  apply (inv_mul_eq_iff_eq_mul₀ hn).mpr
  nlinarith [Real.sq_sqrt hp.le]

lemma collar_coordinates {v e₁ e₂ : Vec} (hv : v ≠ 0)
    (he : e₁ = normalize v) (horth : e₁ ⬝ᵥ e₂ = 0) :
    0 < v ⬝ᵥ e₁ ∧ v ⬝ᵥ e₂ = 0 := by
  refine ⟨?_, ?_⟩
  · rw [he, dot_normalize_self hv]
    exact Real.sqrt_pos.mpr (dot_self_pos hv)
  · calc
      v ⬝ᵥ e₂ = (Real.sqrt (v ⬝ᵥ v) • e₁) ⬝ᵥ e₂ := by rw [he, norm_smul_normalize hv]
      _ = 0 := by rw [smul_dotProduct, horth, smul_zero]

def velocityRadius (v : Vec) (a : ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v + a ^ 2)

lemma velocityRadius_sq (v : Vec) (a : ℝ) :
    velocityRadius v a ^ 2 = v ⬝ᵥ v + a ^ 2 := by
  apply Real.sq_sqrt
  exact add_nonneg (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (sq_nonneg a)

lemma velocityRadius_pos {v : Vec} {a : ℝ} (h : v ≠ 0 ∨ a ≠ 0) :
    0 < velocityRadius v a := by
  apply Real.sqrt_pos.mpr
  rcases h with hv | ha
  · exact add_pos_of_pos_of_nonneg (dot_self_pos hv) (sq_nonneg a)
  · exact add_pos_of_nonneg_of_pos
      (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)) (sq_pos_of_ne_zero ha)

lemma velocityRadius_smoothOn {v : E → Vec} {a : E → ℝ} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, v x ≠ 0 ∨ a x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => velocityRadius (v x) (a x)) U := by
  apply ((dot_smoothOn hv hv).add (ha.pow 2)).sqrt
  intro x hx
  have hp := velocityRadius_pos (hn x hx)
  exact (Real.sqrt_pos.mp hp).ne'

end ClosedSurfaceR4.VelocityFrame

end

end OAI
