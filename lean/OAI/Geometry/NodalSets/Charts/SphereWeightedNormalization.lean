import OAI.Geometry.NodalSets.Charts.SphereReferenceMeasurePositive

namespace OAI

namespace Yau.Target
open Manifold Set
open scoped ContDiff
noncomputable section

lemma sphereWeightedPairing_smul_right (rho u v : Base → ℝ) (t : ℝ) :
    sphereWeightedPairing rho u (t • v) = t*sphereWeightedPairing rho u v := by
  rw [sphereWeightedPairing_symm rho u (t • v),sphereWeightedPairing_smul_left,
    sphereWeightedPairing_symm rho v u]

theorem sphere_weighted_normalization (rho u : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hne : u ≠ 0) :
    ∃ (t : ℝ) (v : Base → ℝ), 0 < t ∧ v = t • u ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧ sphereWeightedPairing rho v v = 1 := by
  have hpos := sphereWeightedPairing_self_pos rho u hr hp hu.continuous hne
  let t := (Real.sqrt (sphereWeightedPairing rho u u))⁻¹
  have ht : 0 < t := inv_pos.mpr (Real.sqrt_pos.mpr hpos)
  refine ⟨t,t • u,ht,rfl,(contMDiff_const (c := t)).mul hu,?_,?_⟩
  · exact smul_ne_zero ht.ne' hne
  · rw [sphereWeightedPairing_smul_left,sphereWeightedPairing_smul_right]
    have hs := Real.sq_sqrt hpos.le
    dsimp [t]
    have hn : Real.sqrt (sphereWeightedPairing rho u u) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    field_simp
    nlinarith only [hs]

lemma sphere_weighted_orthogonal_remainder (rho u v : Base → ℝ)
    (hr : Continuous rho) (hp : ∀ p, 0 < rho p)
    (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hv : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v)
    (hne : u ≠ 0) :
    ∃ (c : ℝ) (w : Base → ℝ), w = v-c • u ∧
      ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ w ∧ sphereWeightedPairing rho w u = 0 ∧
      (w = 0 ↔ v = c • u) := by
  let c := sphereWeightedPairing rho v u / sphereWeightedPairing rho u u
  have hn := (sphereWeightedPairing_self_pos rho u hr hp hu.continuous hne).ne'
  refine ⟨c,v-c • u,rfl,hv.sub ((contMDiff_const (c := c)).mul hu),?_,sub_eq_zero⟩
  have he : v-c • u = v+(-c) • u := by simp only [neg_smul,sub_eq_add_neg]
  rw [he,sphereWeightedPairing_add_left rho v ((-c) • u) u hr hv.continuous
    (((contMDiff_const (c := -c)).mul hu).continuous) hu.continuous,sphereWeightedPairing_smul_left]
  dsimp [c]
  field_simp
  ring

end
end Yau.Target

end OAI
