import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationCutoff
import OAI.Geometry.TamingCompatibility.DifferentialForms.WedgeTransform
import OAI.Geometry.TamingCompatibility.DifferentialForms.PlaneTransverseGraph

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma detInner_comm (u v a b : V) : detInner u v a b = detInner a b u v := by
  simp only [detInner,real_inner_comm u a,real_inner_comm v b,real_inner_comm u b,real_inner_comm v a]
  ring

lemma detInner_le_one (u v a b : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    detInner u v a b ≤ 1 := by
  rw [← inner_skew]
  have hh := real_inner_le_norm u (skew a b v)
  have hh' := norm_skew_le a b v ha hb hab
  rw [hu,one_mul] at hh
  rw [hv] at hh'
  exact hh.trans hh'

lemma skew_error_norm (u v a b : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    ‖u-skew a b v‖ ≤ Real.sqrt (2*(1-detInner u v a b)) := by
  have hh := norm_skew_le a b v ha hb hab
  rw [hv] at hh
  apply (Real.le_sqrt (norm_nonneg _) (by linarith [detInner_le_one u v a b hu hv ha hb hab])).mpr
  rw [norm_sub_sq_real,hu,inner_skew]
  nlinarith [norm_nonneg (skew a b v)]

lemma transverse_add (u v z w : V) :
    transverse u v (z+w) = transverse u v z + transverse u v w := by
  simp only [transverse,inner_add_right,add_smul]
  abel

lemma transverse_skew (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    transverse u v (skew u v w) = 0 := by
  have hvu : ⟪v,u⟫ = 0 := (real_inner_comm _ _).trans huv
  simp only [transverse,skew,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    hu,hv,huv,hvu,one_pow,mul_one,mul_zero,sub_zero,zero_sub,neg_smul]
  abel

lemma norm_transverse_comparison (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ‖transverse u v z‖ ≤ ‖transverse a b z‖ +
      2*Real.sqrt (2*(1-detInner u v a b))*‖z‖ := by
  let δ := Real.sqrt (2*(1-detInner u v a b))
  have hpa : ‖transverse u v a‖ ≤ δ := by
    have he : transverse u v a = transverse u v (a-skew u v b) := by
      rw [transverse_sub,transverse_skew u v b hu hv huv,sub_zero]
    rw [he]
    exact (norm_transverse_le u v _ hu hv huv).trans
      ((skew_error_norm a b u v ha hb hu hv huv).trans_eq (by rw [detInner_comm]))
  have hpb : ‖transverse u v b‖ ≤ δ := by
    have he : transverse u v b = transverse u v (b-skew v u a) := by
      have he' : skew v u a = -skew u v a := by simp only [skew]; abel
      rw [transverse_sub,he',show -skew u v a = (-1:ℝ) • skew u v a by simp,
        transverse_smul,transverse_skew u v a hu hv huv,smul_zero,sub_zero]
    rw [he]
    apply (norm_transverse_le u v _ hu hv huv).trans
    have hh := skew_error_norm b a v u hb ha hv hu ((real_inner_comm _ _).trans huv)
    simpa only [δ,detInner,real_inner_comm b v,real_inner_comm a u,real_inner_comm b u,real_inner_comm a v,
      mul_comm] using hh
  have he : transverse u v z = transverse u v (transverse a b z) +
      ⟪a,z⟫ • transverse u v a + ⟪b,z⟫ • transverse u v b := by
    simp only [transverse,inner_sub_right,inner_smul_right,
      sub_smul,smul_sub,smul_smul]
    module
  have hac : |⟪a,z⟫| ≤ ‖z‖ := by simpa only [ha,one_mul] using abs_real_inner_le_norm a z
  have hbc : |⟪b,z⟫| ≤ ‖z‖ := by simpa only [hb,one_mul] using abs_real_inner_le_norm b z
  calc
    _ ≤ ‖transverse u v (transverse a b z)‖ + ‖⟪a,z⟫ • transverse u v a‖ +
        ‖⟪b,z⟫ • transverse u v b‖ := by rw [he]; exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖transverse a b z‖ + ‖z‖*δ + ‖z‖*δ := by
      simp only [norm_smul,Real.norm_eq_abs]
      exact add_le_add (add_le_add (norm_transverse_le u v _ hu hv huv)
        (mul_le_mul hac hpa (norm_nonneg _) (norm_nonneg _)))
        (mul_le_mul hbc hpb (norm_nonneg _) (norm_nonneg _))
    _ = _ := by dsimp [δ]; ring

lemma first_variation_source_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      5*(1-detInner u v a b)*‖z‖ +
        Real.sqrt (2*(1-detInner u v a b))*‖transverse a b z‖ := by
  have h₁ := first_variation_bound u v a b z hu hv huv ha hb hab
  have h₂ := mul_le_mul_of_nonneg_left (norm_transverse_comparison u v a b z hu hv huv ha hb)
    (Real.sqrt_nonneg (2*(1-detInner u v a b)))
  have hsq := Real.sq_sqrt (show 0 ≤ 2*(1-detInner u v a b) by linarith [detInner_le_one u v a b hu hv ha hb hab])
  have hmul := congrArg (fun t : ℝ => t*‖z‖) hsq
  nlinarith
end TamingCompatibility.PlaneVariation

namespace TamingCompatibility.UnitaryFrame
open PlaneVariation
lemma first_variation_wedge_bound (u v a b z : V)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a,b⟫ = 0) :
    |⟪z,u-skew a b v⟫| ≤
      (5/2:ℝ)*‖wedge u v-wedge a b‖^2*‖z‖ +
        ‖wedge u v-wedge a b‖*‖transverse a b z‖ := by
  have he : ‖wedge u v-wedge a b‖^2 = 2*(1-detInner u v a b) := by
    rw [norm_sub_sq_real,norm_wedge_orthonormal u v hu hv huv,
      norm_wedge_orthonormal a b ha hb hab,wedge_inner]
    unfold detInner
    ring
  have hroot : Real.sqrt (2*(1-detInner u v a b)) = ‖wedge u v-wedge a b‖ := by
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  have hh := first_variation_source_bound u v a b z hu hv huv ha hb hab
  rw [hroot] at hh
  have hmul := congrArg (fun t : ℝ => t*‖z‖) he
  nlinarith
end TamingCompatibility.UnitaryFrame

end
end

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.Concentration
open PlaneVariation UnitaryFrame
lemma cutKernel_plane_variation_bound (η : V → ℝ) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z) (hη1 : ∀ z, η z ≤ 1)
    {a : ℝ} (ha : 0 < a) (hηone : ∀ z, ‖z‖ < a → η z = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → ∀ u v b c z : V,
      ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      ‖b‖ = 1 → ‖c‖ = 1 → inner ℝ b c = 0 →
      |fderiv ℝ (cutKernel η r) z (u-skew b c v)| ≤
        15*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖^2*‖z‖ +
        6*radialCoefficient r ‖z‖*‖wedge u v-wedge b c‖*‖transverse b c z‖ + C*r^4 := by
  obtain ⟨C,hC,hbound⟩ := cutKernel_deriv_bound η hη hηc hη0 hη1 ha hηone
  refine ⟨2*C,by positivity,fun r hr u v b c z hu hv huv hb hc hbc => ?_⟩
  have hw : ‖u-skew b c v‖ ≤ 2 := by
    have hh := norm_skew_le b c v hb hc hbc
    exact (norm_sub_le _ _).trans (by rw [hu,hv] at *; linarith)
  have hvar := first_variation_wedge_bound u v b c z hu hv huv hb hc hbc
  have hh := mul_le_mul_of_nonneg_left hvar (show 0 ≤ (6:ℝ)*radialCoefficient r ‖z‖ from mul_nonneg (by norm_num) (radialCoefficient_nonneg r ‖z‖))
  have hrem := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ C*r^4)
  have hder := hbound r hr z (u-skew b c v)
  nlinarith

lemma sqrt_angular_transverse {χ k δ t : ℝ} (hχ : 0 ≤ χ) (hk : 0 ≤ k)
    (hδ : 0 ≤ δ) (ht : 0 ≤ t) :
    Real.sqrt (χ*δ^2*k)*Real.sqrt (χ*k*t^2) = χ*k*δ*t := by
  rw [←Real.sqrt_mul (by positivity)]
  have he : χ*δ^2*k*(χ*k*t^2) = (χ*k*δ*t)^2 := by ring
  rw [he,Real.sqrt_sq (by positivity)]
end TamingCompatibility.Concentration

end
end

end OAI
