import OAI.Geometry.Relativity.CKS.OuterBounds

namespace OAI

noncomputable section
namespace CKSSphericalChart
noncomputable section
open Set Filter CKSCalculus CKSRealizedRound CKSSphericalHarmonics CKSInducedSphere CKSBending CKSLocalBending
open scoped Topology ContDiff

theorem constructed_outer_DEC (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀) (m : ℝ) :
    ∃ R₀ : ℝ, 12 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ x : Point,
    3*R ≤ x 0 → Real.sin (x 1) ≠ 0 →
    DEC (metricJet (lapse (outerMass f₀ m R) (bendingV R)) x)
      (tensorJet (lapse (outerMass f₀ m R) (bendingV R)) (bendingV R)
        (radial (normalEntry (bendingV R) (bendingBeta R)))
        (correctedComponent (bendingV R) (outerA f₀ R))
        (correctedComponent (bendingV R) (outerPhi f₀ R)) x) := by
  obtain ⟨M,B,T,hM,hB,hT,hbound⟩ := outer_uniform_bounds f₀ hf₀ m
  obtain ⟨V,hV,hvbound⟩ := bending_reduced_bound
  let Q := (energyError M B V T + momentumError M B V T)^2
  refine ⟨max 12 (max (4*M) Q),le_max_left _ _,?_⟩
  intro R hR x hr hs
  have hR12 : 12 ≤ R := (le_max_left _ _).trans hR
  have hRmass : 4*M ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRerr : Q ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hRp : 0 < R := by linarith
  have hrp : 0 < x 0 := by linarith
  have hxm : x ∈ positiveChart := hrp
  have hF := (outerMass_smooth f₀ hf₀ m hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hv := (bendingV_smooth hRp).contDiffAt (isOpen_Ioi.mem_nhds hrp)
  have ha := (outerA_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  have hb := (outerPhi_smooth f₀ hf₀ hRp).contDiffAt (positiveChart_open.mem_nhds hxm)
  obtain ⟨hm,hΔ,hg,ht⟩ := hbound R hR12 x hr hs
  obtain ⟨hdθ,hdφ⟩ := outer_divergence f₀ hf₀ m hRp hrp hs
  exact smooth_outer_DEC
    (hF.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (hv.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    ((bendingBeta_smooth R).differentiable (by simp) _)
    (ha.differentiableAt (by simp)) (hb.differentiableAt (by simp))
    (by linarith) hs hm (by linarith)
    (outerMass_heat f₀ hf₀ m hRp hr hs) hdθ hdφ
    (beta_nonneg _) (beta_le_one _) (beta_support hR12)
    (zeta_nonneg _) (zeta_le_one _) (zeta_support hR12)
    hΔ hg hV hT (hvbound R hR12 (x 0) hrp) ht (by dsimp [Q] at hRerr; linarith)

lemma constructed_outer_mass_initial (f₀ : C(Sphere,ℝ)) (hf₀ : SmoothSphere f₀)
    (m : ℝ) (hb : Balanced f₀ m) {R : ℝ} (hR : 0 < R)
    {x : Point} (hr : x 0 ≤ 4*R) :
    outerMass f₀ m R x = paddingMass R (x 0) + f₀ ⟨sphereParam x,by simpa only [Metric.mem_sphere,dist_zero_right] using sphereParam_norm x⟩ := by
  unfold outerMass chartMass
  rw [heatTime_initial hR hr]
  congr 1
  exact canonicalF_initial f₀ hf₀ m hb
    ⟨sphereParam x,by simpa only [Metric.mem_sphere,dist_zero_right] using sphereParam_norm x⟩

end
end CKSSphericalChart

end

end OAI
