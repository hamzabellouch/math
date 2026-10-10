import OAI.Geometry.NodalSets.Charts.SphereSimplicityRigidity
import OAI.Geometry.NodalSets.Persistence.SphereWeakUniqueContinuation
import OAI.Geometry.NodalSets.Spectral.IntrinsicEigenfunctionLinearity

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Filter MeasureTheory
open scoped ContDiff Topology
noncomputable section

lemma sphere_simplicity_self_energy_zero (u a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam u u = 0 := by
  rw [sphere_simplicity_energy_eq_coordinate u u a b hu zeta lam ha hb,
    (round_simplicity_energy_identity (u ∘ seedSphereFromCoord) (u ∘ seedSphereFromCoord) zeta (spherePullback_smooth u hu seedPoint)
      (spherePullback_smooth u hu seedPoint) hz hc lam hlam).2]
  simp [roundSimplicitySquare]

theorem sphere_simplicity_zero_energy_global (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0)
    (lam : ℝ) (hlam : lam ≠ 0)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (hzpos : ∃ x, 0 < zeta x)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (henergy : sphereEnergyForm a b lam v v = 0) : ∃ c : ℝ, ∀ p, v p = c*u p := by
  let O := {x : Yau.Jets.Coord | 0 < zeta x}
  have hO : IsOpen O := isOpen_lt continuous_const hz.continuous
  obtain ⟨p,⟨x,hxz,rfl⟩,hxu⟩ := sphere_eigenfunction_nonzero_on_open A hA hs hp rho hr hrp u hu lam
    heu hune (seedSphereFromCoord '' O) (sphereChartCoordMap_isOpenMap seedPoint O hO)
    (Set.Nonempty.image _ hzpos)
  obtain ⟨c,U,hU,hxU,hlocal⟩ := sphere_simplicity_local_ball u v a b hu hv zeta hz hc hzn lam hlam
    ha hb henergy x hxz hxu
  let w := fun p : Base ↦ (-c)*u p+v p
  have hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w := (contMDiff_const.mul hu).add hv
  have hew : ∀ p z, -intrinsicWeightedChartOperator A rho w p z = lam*w ((extChartAt (𝓡 4) p).symm z) :=
    intrinsic_eigenfunction_linear_combination A hA hs hp rho u v hu hv lam heu hev (-c)
  have hw0 : w =ᶠ[𝓝 (seedSphereFromCoord x)] (fun _ ↦ 0) := by
    filter_upwards [hU.mem_nhds hxU] with p hpU
    dsimp [w]
    rw [hlocal p hpU]
    ring
  have hglobal := sphere_weak_unique_continuation A hA hs hp rho hr hrp w hw lam hew
    (seedSphereFromCoord x) hw0
  refine ⟨c,?_⟩
  intro p
  have hh := congrFun hglobal p
  change (-c)*u p+v p=0 at hh
  linarith

theorem sphere_simplicity_energy_kernel_iff (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ p v w, A p v w = A p w v) (hp : ∀ p v, v ≠ 0 → 0 < A p v v)
    (rho : Base → ℝ) (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ p, 0 < rho p)
    (u v a b : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (hune : u ≠ 0)
    (lam : ℝ) (hlam : lam ≠ 0)
    (heu : ∀ p z, -intrinsicWeightedChartOperator A rho u p z = lam*u ((extChartAt (𝓡 4) p).symm z))
    (hev : ∀ p z, -intrinsicWeightedChartOperator A rho v p z = lam*v ((extChartAt (𝓡 4) p).symm z))
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (hzn : ∀ x, 0 ≤ zeta x) (hzpos : ∃ x, 0 < zeta x)
    (ha : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hb : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x) :
    sphereEnergyForm a b lam v v = 0 ↔ ∃ c : ℝ, ∀ p, v p = c*u p := by
  constructor
  · exact sphere_simplicity_zero_energy_global A hA hs hp rho hr hrp u v a b hu hv hune lam hlam
      heu hev zeta hz hc hzn hzpos ha hb
  · rintro ⟨c,hcval⟩
    have hvval : v = c • u := funext hcval
    rw [hvval,sphereEnergyForm_smul_left a b lam u _ hu,
      sphereEnergyForm_smul_right a b lam u u hu,
      sphere_simplicity_self_energy_zero u a b hu zeta hz hc lam hlam ha hb,mul_zero,mul_zero]

end
end Yau.Target

end OAI
