import Mathlib
import OAI.Analysis.AffineBernstein.SectionNormalizationFamily
import OAI.Analysis.AffineBernstein.NormalizedFamilyDet

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section GlobalDetRatio

lemma det_hessian_normalizedFunction {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (A : Space n ≃L[ℝ] Space n) (t : ℝ) (x : Space n) :
    (hessian (normalizedFunction u A t) x).det =
      (t⁻¹)^n * (cleMatrix A).det^2 * (hessian u (A x)).det := by
  rw [hessian_normalizedFunction hu,det_affine_congruence]

/-- Genuine global determinant-ratio bounds follow from the uniform balanced
section normalizations. This is a consequence of the original PDE, rather
than a global determinant assumption. It does not imply individual Hessian
bounds. -/
theorem centered_balanced_global_det_ratio {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hm : AffineMaximalOn univ u) (hu0 : u 0=0) (hdu0 : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : Space n,
      c * (hessian u 0).det ≤ (hessian u x).det ∧
      (hessian u x).det ≤ C * (hessian u 0).det := by
  obtain ⟨R,hR,Hfam⟩ := centered_section_normalization_family hn hu hp hu0 hdu0 hρ hρ1 hbal
  obtain ⟨c,C,hc,hC,Hb⟩ := normalized_balanced_det_bounds hρ hρ1 hR (n := n)
  refine ⟨c/C,C/c,div_pos hc hC,div_pos hC hc,?_⟩
  intro x
  let t := max 1 (u ((16*R) • x))+1
  have ht : 0 < t := by dsimp [t]; have := le_max_left 1 (u ((16*R) • x)); linarith
  have htx : u ((16*R) • x)<t := by
    dsimp [t]
    have := le_max_right 1 (u ((16*R) • x))
    linarith
  obtain ⟨A,hin,hout⟩ := Hfam t ht
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hpv := posDef_hessian_normalizedFunction hu hp A ht
  have hvm := affineMaximalOn_normalizedFunction hu hp hm A ht
  have hv0 : v 0=0 := by simp [v,normalizedFunction,hu0]
  have hdv0 : fderiv ℝ v 0=0 := by simp [v,fderiv_normalizedFunction hu,hdu0]
  have hbalv := sectionBalance_normalizedFunction hu hp hbal A ht
  have hysection : (16*R) • A.symm x ∈ tangentSection univ v 0 1 := by
    refine ⟨mem_univ _,?_⟩
    simp only [tangentHeight,hv0,hdv0,sub_zero,zero_apply]
    change t⁻¹*u (A ((16*R) • A.symm x)) < 1
    rw [map_smul,A.apply_symm_apply,mul_comm,← div_eq_mul_inv]
    exact (div_lt_one ht).mpr htx
  have hyr := mem_ball_zero_iff.mp (hout hysection)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 16*R)] at hyr
  have hy : A.symm x ∈ Metric.ball (0:Space n) (1/8:ℝ) := by
    rw [mem_ball_zero_iff]
    nlinarith
  have H := Hb v hv hpv hvm hv0 hdv0 hbalv hin hout
  have H0 := H 0 (by simp : (0:Space n) ∈ Metric.ball 0 (1/8:ℝ))
  have Hx := H (A.symm x) hy
  dsimp only [v] at H0 Hx
  rw [det_hessian_normalizedFunction hu, map_zero] at H0
  rw [det_hessian_normalizedFunction hu, A.apply_symm_apply] at Hx
  let q := (t⁻¹)^n * (cleMatrix A).det^2
  have hq : 0 < q := mul_pos (pow_pos (inv_pos.mpr ht) _) (sq_pos_of_ne_zero (cleMatrix_det_ne_zero A))
  change c ≤ q*(hessian u 0).det ∧ q*(hessian u 0).det ≤ C at H0
  change c ≤ q*(hessian u x).det ∧ q*(hessian u x).det ≤ C at Hx
  constructor
  · apply (mul_le_mul_iff_right₀ hq).mp
    have hh := mul_le_mul_of_nonneg_left H0.2 (div_nonneg hc.le hC.le)
    have he : (c/C)*C=c := div_mul_cancel₀ c hC.ne'
    rw [he] at hh
    calc
      q * ((c/C)*(hessian u 0).det) = (c/C)*(q*(hessian u 0).det) := by ring
      _ ≤ c := hh
      _ ≤ q*(hessian u x).det := Hx.1
  · apply (mul_le_mul_iff_right₀ hq).mp
    have hh := mul_le_mul_of_nonneg_left H0.1 (div_nonneg hC.le hc.le)
    have he : (C/c)*c=C := div_mul_cancel₀ C hc.ne'
    rw [he] at hh
    calc
      q*(hessian u x).det ≤ C := Hx.2
      _ ≤ (C/c)*(q*(hessian u 0).det) := hh
      _ = q*((C/c)*(hessian u 0).det) := by ring

end GlobalDetRatio


end
end AffineBernstein
end

end OAI
