import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreMismatch
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialBandMeasure

namespace OAI

/-! # The second actual core is small outside the finite exceptional speed list -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.AxialFlow

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem second_core_small_off_bands {α γ q a δ : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hq₁ : 1 < q) (hq₂ : q < 2)
    (ha : 0 < a) (hδ : 0 < δ) :
    ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ b : ℝ, 0 < b → ∀ ε : ℝ, 0 < ε →
      ∃ r : ℝ, 0 < r ∧ ∀ {K s d t₁ t₂ z : ℝ},
      0 ≤ K → 0 < s → 0 < d → d ≤ 1/16 → d ≤ min δ b/4 → a ≤ t₂ → t₂ ≤ t₁ →
      ∀ (η : ℝ) (sign : Bool) (y : Transverse) (v : Velocity) (S : Finset ℝ),
      (μ₀ ≤ s → s ∈ S) → transverse v ≠ 0 → ‖transverse v‖ ≤ r →
      axial v ∉ bands (collapsedCenters α t₁ z) δ →
      axial v ∉ bands (profileCenters α γ t₁ z S) b →
      normalizedCoreKernel η K α γ s d q sign
        ((t₂,(y,z-(t₁-t₂)*axial v)),v) univ ≤
        ENNReal.ofReal (amplitude K α γ s t₂)*ENNReal.ofReal ε := by
  obtain ⟨μ₀,hμ₀,hsmall⟩ := outside_collapsedBands_second_gap hα hγ ha hδ
  refine ⟨μ₀,hμ₀,?_⟩
  intro b hb ε hε
  have hc : 0 < min δ b/4 := div_pos (lt_min hδ hb) (by norm_num)
  obtain ⟨r,hr,hcore⟩ := core_mass_small_of_speed_gap (α := α) hq₁ hq₂ hc hε
  refine ⟨r,hr,?_⟩
  intro K s d t₁ t₂ z hK hs hd hdmax hdc ht₂ htt η sign y v S hS hv hvr hcollapsed hprofile
  apply hcore hK hα hγ hs hd hdmax (ha.le.trans ht₂) η sign
    (y,z-(t₁-t₂)*axial v) v hv hvr
  have hsign : JetPrototype.sign sign = 1 ∨ JetPrototype.sign sign = -1 := by
    cases sign <;> simp [JetPrototype.sign]
  have hbound : min δ b/4+d ≤ min δ b/2 := by linarith
  by_cases hss : s < μ₀
  · have hg := hsmall (JetPrototype.sign sign) s 0 t₁ t₂ z (axial v) 0
      hsign hs hss ht₂ htt (by simpa using div_pos hδ (by norm_num : (0:ℝ)<4)) hcollapsed
    simp only [JetCoreMap.axialMap,mul_zero,zero_add,sub_zero] at hg
    exact hbound.trans ((by linarith [min_le_left δ b] : min δ b/2 ≤ δ/2).trans hg)
  · have hg := outside_profileBands_second_gap (b := b) (w := axial v)
      hα.le hγ.le hs (ha.le.trans ht₂) htt
      S (hS (le_of_not_gt hss)) hprofile (d := 0) (ω := 0)
      (show |(0 : ℝ)*0| ≤ b/2 by simpa using (half_pos hb).le)
      (JetPrototype.sign sign) hsign
    simp only [JetCoreMap.axialMap,mul_zero,zero_add,sub_zero] at hg
    exact hbound.trans ((by linarith [min_le_right δ b] : min δ b/2 ≤ b/2).trans hg)

end BoltzmannNonuniqueness.JetCoreSheet

end

end OAI
