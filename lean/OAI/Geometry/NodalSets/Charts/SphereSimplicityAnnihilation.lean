import OAI.Geometry.NodalSets.Charts.SphereSimplicityEnergy

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance sphereSimplicityAnnihilationLocal1 : MeasurableSpace Base := borel Base
local instance sphereSimplicityAnnihilationLocal2 : BorelSpace Base := ⟨rfl⟩

lemma sphereCrossDifferential_self (u : Base → ℝ) (p : Base) : sphereCrossDifferential u u p = 0 := by
  simp [sphereCrossDifferential]

lemma sphereCrossDifferential_add_self (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereCrossDifferential u (u+v) p = sphereCrossDifferential u v p := by
  simp only [sphereCrossDifferential,sphereDifferential_add u v hu hv,Pi.add_apply,smul_add,add_smul]
  abel

theorem sphere_simplicity_form_annihilates (u a b Z : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (zeta : Yau.Jets.Coord → ℝ) (hz : ContDiff ℝ ∞ zeta) (hc : HasCompactSupport zeta)
    (lam : ℝ) (hlam : lam ≠ 0)
    (haval : ∀ x, a (seedSphereFromCoord x) = zeta x*u (seedSphereFromCoord x)^2)
    (hbval : ∀ x, b (seedSphereFromCoord x) = simplicityDensityPerturbation roundCoordDensity
      (u ∘ seedSphereFromCoord) zeta (roundCoordGradient (u ∘ seedSphereFromCoord)) lam x)
    (hZ : ∀ x, Z (seedSphereFromCoord x) = zeta x)
    (v : Base → ℝ) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) :
    sphereEnergyForm a b lam u v = 0 := by
  have hself := (sphere_simplicity_energy_identity u u a b Z hu hu zeta hz hc lam hlam haval hbval hZ).2.2
  have hsum := (sphere_simplicity_energy_identity u (u+v) a b Z hu (hu.add hv) zeta hz hc lam hlam haval hbval hZ).2.2
  have hvv := (sphere_simplicity_energy_identity u v a b Z hu hv zeta hz hc lam hlam haval hbval hZ).2.2
  have hzero : sphereEnergyForm a b lam u u = 0 := by
    simpa only [sphereCrossDifferential_self,map_zero,mul_zero,integral_zero] using hself
  have heq : sphereEnergyForm a b lam (u+v) (u+v) = sphereEnergyForm a b lam v v := by
    rw [hsum,hvv]
    simp only [sphereCrossDifferential_add_self u v hu hv]
  rw [sphereEnergyForm_add_left a b ha hb hQ haQ hbQ lam u v (u+v) hu hv (hu.add hv),
    sphereEnergyForm_add_right a b ha hb hQ haQ hbQ lam u u v hu hu hv,
    sphereEnergyForm_add_right a b ha hb hQ haQ hbQ lam v u v hv hu hv,hzero,
    sphereEnergyForm_symm a b lam v u] at heq
  linarith

end
end Yau.Target

end OAI
