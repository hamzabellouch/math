import Mathlib
import OAI.Analysis.WeakInfiniteness.SeparationMetric

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma separation_four_column_bounds (a b e f Z W w : B)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hef : e*f=0)
    {l : ℝ} (hl : 0 < l)
    (hen : ‖e‖ ≤ 1) (hfn : ‖f‖ ≤ 1) (hZ : ‖Z‖ ≤ 2) (hWn : ‖W‖ ≤ 2)
    (hgf : cfc (separationG l) (star (a*b)*(a*b))*f=f)
    (hW : W=1+cfc (separationG l) (star (a*b)*(a*b))*w*cfc (separationG l) (star (a*b)*(a*b)))
    (hZW : star Z*W=1) :
    let X := a*b
    let T := star X*X
    let S := X*star X
    let C₁ := a*X*cfc (separationV l) T
    let C₂ := b*cfc (separationR l) T
    let x₀ := a*cfc (separationL l) S
    let y₀ := b*cfc (separationL l) T
    let x₁ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (C₁*Z*e)
    let y₁ := (((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (C₂*W*f)
    ‖star x₀*y₀‖ ≤ 8*l ∧ ‖star x₁*y₀‖ ≤ 6*Real.sqrt l ∧
      ‖star x₀*y₁‖ ≤ 6*Real.sqrt l ∧ star x₁*y₁=0 := by
  dsimp only
  let X := a*b
  let T := star X*X
  let S := X*star X
  let V := cfc (separationV l) T
  let R := cfc (separationR l) T
  let Lₛ := cfc (separationL l) S
  let Lₜ := cfc (separationL l) T
  have hV : IsSelfAdjoint V := cfc_predicate _ _
  have hLs : IsSelfAdjoint Lₛ := cfc_predicate _ _
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hscale : (Real.sqrt l)⁻¹*l=Real.sqrt l := by
    have hsq := Real.sq_sqrt hl.le
    field_simp
    nlinarith
  have hs_norm : ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ)‖=(Real.sqrt l)⁻¹ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hroot)]
  have hx0 : star (a*Lₛ)*(b*Lₜ)=Lₛ*X*Lₜ := by
    rw [star_mul,hLs.star_eq,ha.star_eq]
    dsimp only [X]
    simp only [mul_assoc]
  have hx1 : star (a*X*V*Z*e)*(b*Lₜ)=e*star Z*(V*T*Lₜ) := by
    rw [star_mul (a*X*V*Z) e,star_mul (a*X*V) Z,star_mul (a*X) V,star_mul a X,
      he.star_eq,hV.star_eq,ha.star_eq]
    dsimp only [T,X]
    simp only [mul_assoc]
  have hxy1 : star (a*Lₛ)*(b*R*W*f)=(Lₛ*X*R)*W*f := by
    rw [star_mul,hLs.star_eq,ha.star_eq]
    dsimp only [X]
    simp only [mul_assoc]
  refine ⟨?_,?_,?_,?_⟩
  · change ‖star (a*Lₛ)*(b*Lₜ)‖ ≤ _
    rw [hx0]
    exact norm_separation_low X hl
  · change ‖star ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (a*X*V*Z*e))*(b*Lₜ)‖ ≤ _
    rw [star_smul,Complex.star_def,Complex.conj_ofReal,smul_mul_assoc,hx1,norm_smul,hs_norm]
    have hn : ‖e*star Z*(V*T*Lₜ)‖ ≤ 1*2*(3*l) := by
      apply (norm_mul_le _ _).trans
      apply mul_le_mul _ (norm_separation_mixedV X hl) (norm_nonneg _) (by positivity)
      apply (norm_mul_le _ _).trans
      rw [norm_star]
      gcongr
    calc
      _≤(Real.sqrt l)⁻¹*(1*2*(3*l)) := mul_le_mul_of_nonneg_left hn (by positivity)
      _=6*Real.sqrt l := by nlinarith [hscale]
  · change ‖star (a*Lₛ)*((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (b*R*W*f))‖ ≤ _
    rw [mul_smul_comm,hxy1,norm_smul,hs_norm]
    have hn : ‖(Lₛ*X*R)*W*f‖ ≤ (3*l)*2*1 := by
      exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)).trans
        (by gcongr; exact norm_separation_mixedR X hl))
    calc
      _≤(Real.sqrt l)⁻¹*((3*l)*2*1) := mul_le_mul_of_nonneg_left hn (by positivity)
      _=6*Real.sqrt l := by nlinarith [hscale]
  · change star ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (a*X*V*Z*e))*
      ((((Real.sqrt l)⁻¹ : ℝ) : ℂ) • (b*R*W*f))=0
    rw [star_smul,smul_mul_assoc,mul_smul_comm]
    have hh : star (a*X*V*Z*e)*(b*R*W*f)=0 := compatible_columns_orthogonal
      (a*X*V) (b*R) (cfc (separationG l) T) e f Z W w l he.isSelfAdjoint hef hgf hW hZW
      (separation_metric_identity a b ha.isSelfAdjoint hl)
    rw [hh,smul_zero,smul_zero]

end

end

end WeakPureInfiniteness
end

end OAI
