import OAI.Analysis.CircleDomains.Sobolev.ModelUniformRowEnergy

namespace OAI

/-! A common explicit L2 budget for the actual model's joint reference
differential, obtained from image area and holomorphic row equality. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem working_joint_norm_le (M : CompactScalarModel G u)
    (hG : IsOpen G) (hinf : OnePoint.infty ∈ G) (L : ℝ)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ z : ℂ, (z : Sphere) ∈ G → z ∈ ball 0 L → ‖M.function z‖ ≤ K)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ 2*(Real.pi*K^2+1) := by
  have hE := M.working_row_energy_le hG hinf L hK hbound Wx
  have hn := integral_sq_eq_eLpNorm_toReal_sq Wx.weakGrad_norm_memLp
  rw [eLpNorm_norm _ Wx.weakGrad_memLp.aestronglyMeasurable] at hn
  rw [hn] at hE
  have hrow : (eLpNorm Wx.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤
      Real.pi*K^2+1 := by
    have ha : 0 ≤ Real.pi*K^2 := mul_nonneg Real.pi_pos.le (sq_nonneg _)
    nlinarith [sq_nonneg ((eLpNorm Wx.weakGrad 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal-1)]
  have heq := eLpNorm_congr_norm_ae Wx.weakGrad_memLp.aestronglyMeasurable
    Wy.weakGrad_memLp.aestronglyMeasurable (M.working_rows_norm_eq hG hinf L Wx Wy) (p := 2)
  have hb := (weakPairDifferential_memLp Wx.weakGrad_memLp Wy.weakGrad_memLp).2
  rw [← heq] at hb
  linarith


 theorem uniform_working_joint_norm (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    {R L : ℝ} (hR : 0 < R)
    (hsource : (((↑) : ℂ → Sphere) '' ball 0 R)ᶜ ⊆ G) (hL : L ≤ 4*R)
    (Wx : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).re)
      (physicalPlaneDomain G ∩ ball 0 L))
    (Wy : DeGiorgi.MemW1pWitness 2 (fun x => (M.function (complexPlaneCoordinates x)).im)
      (physicalPlaneDomain G ∩ ball 0 L)) :
    (eLpNorm (fun x => weakPairDifferential (Wx.weakGrad x) (Wy.weakGrad x)) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 L))).toReal ≤ 2*(Real.pi*(5*R)^2+1) := by
  have hb := (M.uniform_omitted_and_image_bound harea hG hR hsource).2
  apply M.working_joint_norm_le hG hinf L (by positivity) _ Wx Wy
  intro z hz hzL
  apply hb z hz
  exact (by simpa only [mem_ball, dist_zero_right] using hzL : ‖z‖ < L).le.trans hL

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
