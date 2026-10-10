import Mathlib
import OAI.Geometry.CAT0Fillings.Model
import OAI.Geometry.CAT0Fillings.Radial.MetricDerivative
import OAI.Geometry.CAT0Fillings.Radial.UniformSlope

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix Set Metric
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma metricSpatialRadialForm_congruence (G Q : Matrix ι ι ℝ)
    (hQ : Q.transpose = Q) (hi : IsUnit Q.det) (hG : G = Q*Q)
    (g r t : ℝ) (α γ : ι → ℝ) :
    Q⁻¹ * metricSpatialRadialForm G g r t α γ * Q⁻¹ =
      spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ) := by
  have hs : (Q⁻¹).transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,hQ]
  have h0 : Q⁻¹*G*Q⁻¹ = 1 := by
    rw [hG,←mul_assoc,Matrix.nonsing_inv_mul Q hi,one_mul,Matrix.mul_nonsing_inv Q hi]
  have ho (a b : ι → ℝ) : Q⁻¹*vecMulVec a b*Q⁻¹ =
      vecMulVec (Q⁻¹.mulVec a) (Q⁻¹.mulVec b) := by
    rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,←Matrix.mulVec_transpose,hs]
  have he : spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ) =
      (1-t*g)^2 • (1 : Matrix ι ι ℝ)-((1-t*g)*t*r) •
        (vecMulVec (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)+
          vecMulVec (Q⁻¹.mulVec γ) (Q⁻¹.mulVec α))+
        (t^2*r^2) • vecMulVec (Q⁻¹.mulVec γ) (Q⁻¹.mulVec γ) := by
    ext i j
    simp only [spatialRadialForm,Matrix.of_apply,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.one_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    ring
  rw [he,metricSpatialRadialForm]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Matrix.mul_smul,Matrix.smul_mul,ho,h0]

lemma metricSpatialRadialForm_normalized_by_sqrt (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (g r t : ℝ) (α γ : ι → ℝ) :
    Real.sqrt (metricSpatialRadialForm G g r t α γ).det / Real.sqrt G.det =
      Real.sqrt (spatialRadialForm g r t ((CFC.sqrt G)⁻¹.mulVec α)
        ((CFC.sqrt G)⁻¹.mulVec γ)).det := by
  let Q := CFC.sqrt G
  have hs : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg G).posSemidef.isHermitian).eq
  have hQ : Q.det = Real.sqrt G.det := by
    simpa only [RCLike.sqrt_real] using hG.posSemidef.det_sqrt
  have hi : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by rw [hQ]; exact (Real.sqrt_pos.2 hG.det_pos).ne')
  have hh := congrArg Matrix.det (metricSpatialRadialForm_congruence G Q hs hi
    (by simpa only [pow_two] using (CFC.sq_sqrt G hG.posSemidef.nonneg).symm) g r t α γ)
  simp only [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv] at hh
  have hn : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hG.det_pos).ne'
  have he : (spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)).det =
      (metricSpatialRadialForm G g r t α γ).det / G.det := by
    rw [←hh,hQ]
    calc
      _ = (metricSpatialRadialForm G g r t α γ).det / (Real.sqrt G.det)^2 := by
        field_simp
      _ = _ := by rw [Real.sq_sqrt hG.det_pos.le]
  change _ = Real.sqrt (spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)).det
  rw [he,Real.sqrt_div' _ hG.det_pos.le]

lemma inverse_sqrt_mulVec_norm_le (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (a : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ v : ι → ℝ, (a ⬝ᵥ v)^2 ≤ K^2*(v ⬝ᵥ G.mulVec v)) :
    ‖(CFC.sqrt G)⁻¹.mulVec a‖ ≤ K := by
  let Q := CFC.sqrt G
  have hs : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg G).posSemidef.isHermitian).eq
  have hsi : (Q⁻¹).transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,hs]
  have hQ : Q.det = Real.sqrt G.det := by
    simpa only [RCLike.sqrt_real] using hG.posSemidef.det_sqrt
  have hi : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by rw [hQ]; exact (Real.sqrt_pos.2 hG.det_pos).ne')
  have hv (v : ι → ℝ) : (Q⁻¹.mulVec v) ⬝ᵥ G.mulVec (Q⁻¹.mulVec v) = v ⬝ᵥ v := by
    have hGQ : G = Q*Q := by
      simpa only [pow_two] using (CFC.sq_sqrt G hG.posSemidef.nonneg).symm
    rw [hGQ,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hs,
      Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hi,Matrix.one_mulVec]
  apply (pi_norm_le_iff_of_nonneg hK).2
  intro j
  have hh := ha (Q⁻¹.mulVec (Pi.single j 1))
  rw [hv] at hh
  have he : a ⬝ᵥ Q⁻¹.mulVec (Pi.single j 1) = Q⁻¹.mulVec a j := by
    rw [Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hsi]
    simp
  rw [he] at hh
  have he' : (Pi.single j (1:ℝ)) ⬝ᵥ Pi.single j 1 = 1 := by simp
  rw [he',mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) hK).1 (by simpa only [Real.norm_eq_abs,sq_abs] using hh)

theorem metricSpatialRadialForm_intrinsic_uniform_slope_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Matrix ι ι ℝ), G.PosDef →
      ∀ g r : ℝ, |g| ≤ B → |r| ≤ B → ∀ α γ : ι → ℝ,
      (∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ G.mulVec v)) →
      (∀ v : ι → ℝ, (γ ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ G.mulVec v)) →
      ∀ t ∈ Icc (0:ℝ) 1,
      |Real.sqrt (metricSpatialRadialForm G g r t α γ).det / Real.sqrt G.det-1| ≤ C*t := by
  obtain ⟨C,hC,hbound⟩ := spatialRadialForm_uniform_slope_bound (ι := ι) B
  refine ⟨C,hC,?_⟩
  intro G hG g r hg hr α γ hα hγ t ht
  rw [metricSpatialRadialForm_normalized_by_sqrt G hG]
  apply hbound ⟨⟨g,r⟩,⟨_,_⟩⟩ _ t ht
  simp only [Prod.norm_def,Real.norm_eq_abs,max_le_iff]
  exact ⟨⟨hg,hr⟩,inverse_sqrt_mulVec_norm_le G hG α B hB hα,
    inverse_sqrt_mulVec_norm_le G hG γ B hB hγ⟩

end CAT0Fillings
end
end

end OAI
