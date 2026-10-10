import OAI.Geometry.NodalSets.Charts.SphereEnergyForm

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set MeasureTheory
open scoped ContDiff
noncomputable section
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace
local instance sphereEnergyBilinearLocal1 : MeasurableSpace Base := borel Base
local instance sphereEnergyBilinearLocal2 : BorelSpace Base := ⟨rfl⟩

lemma sphereDifferential_add (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereDifferential (u+v) p = sphereDifferential u p+sphereDifferential v p :=
  mfderiv_add (hu.mdifferentiable (by simp) p) (hv.mdifferentiable (by simp) p)

lemma sphereDifferential_smul (u : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) (p : Base) :
    sphereDifferential (t • u) p = t • sphereDifferential u p :=
  const_smul_mfderiv (hu.mdifferentiable (by simp) p) t

lemma sphereEnergyDensity_add_left (a b : Base → ℝ) (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (p : Base) :
    sphereEnergyDensity a b lam (u+v) w p =
      sphereEnergyDensity a b lam u w p+sphereEnergyDensity a b lam v w p := by
  simp only [sphereEnergyDensity,sphereDifferential_add u v hu hv, map_add,
    _root_.add_apply,Pi.add_apply]
  ring

lemma sphereEnergyForm_add_left (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereEnergyForm a b lam (u+v) w = sphereEnergyForm a b lam u w+sphereEnergyForm a b lam v w := by
  simp only [sphereEnergyForm,sphereEnergyDensity_add_left a b lam u v w hu hv]
  exact integral_add (sphereEnergyDensity_integrable a b ha hb hQ haQ hbQ lam u w hu hw)
    (sphereEnergyDensity_integrable a b ha hb hQ haQ hbQ lam v w hv hw)

lemma sphereEnergyForm_smul_left (a b : Base → ℝ) (lam : ℝ) (u v : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (t : ℝ) :
    sphereEnergyForm a b lam (t • u) v = t*sphereEnergyForm a b lam u v := by
  have he (p : Base) : sphereEnergyDensity a b lam (t • u) v p = t*sphereEnergyDensity a b lam u v p := by
    simp only [sphereEnergyDensity,sphereDifferential_smul u hu, map_smul,
      _root_.smul_apply,Pi.smul_apply,smul_eq_mul]
    ring
  simp only [sphereEnergyForm,he]
  exact integral_const_mul t _

lemma sphereEnergyForm_add_right (a b : Base → ℝ)
    (ha : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b)
    {Q : Set Yau.Jets.Coord} (hQ : IsCompact Q)
    (haQ : tsupport a ⊆ seedSphereFromCoord '' Q) (hbQ : tsupport b ⊆ seedSphereFromCoord '' Q)
    (lam : ℝ) (u v w : Base → ℝ)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hw : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w) :
    sphereEnergyForm a b lam u (v+w) = sphereEnergyForm a b lam u v+sphereEnergyForm a b lam u w := by
  rw [sphereEnergyForm_symm a b lam u (v+w),sphereEnergyForm_add_left a b ha hb hQ haQ hbQ lam v w u hv hw hu,
    sphereEnergyForm_symm a b lam v u,sphereEnergyForm_symm a b lam w u]

lemma sphereEnergyForm_smul_right (a b : Base → ℝ) (lam : ℝ) (u v : Base → ℝ)
    (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v) (t : ℝ) :
    sphereEnergyForm a b lam u (t • v) = t*sphereEnergyForm a b lam u v := by
  rw [sphereEnergyForm_symm a b lam u (t • v),sphereEnergyForm_smul_left a b lam v u hv t,
    sphereEnergyForm_symm a b lam v u]

end
end Yau.Target

end OAI
