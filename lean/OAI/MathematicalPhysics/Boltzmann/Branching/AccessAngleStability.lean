import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveAccessAngles
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceCollisionGeometry

namespace OAI

/-! # The fixed entry angles remain effective for nearby measurable partners -/

noncomputable section

open Set Metric

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem child_opposite_unit (e n : V) (he : ‖e‖ = 1) : child e (-e) n = n := by
  have hd : e-(-e) = (2:ℝ) • e := by module
  simp [child,hd,norm_smul,he]

theorem relative_distance_lower (v w u z : V) :
    ‖u-z‖-‖v-u‖-‖w-z‖ ≤ ‖v-w‖ := by
  have he : u-z = (u-v)+(v-w)+(w-z) := by module
  have hh : ‖u-z‖ ≤ ‖u-v‖+‖v-w‖+‖w-z‖ := by
    rw [he]
    have h₁ := norm_add_le (u-v) (v-w)
    have h₂ := norm_add_le ((u-v)+(v-w)) (w-z)
    linarith
  rw [norm_sub_rev u v] at hh
  linarith

theorem access_pair_stability {κ ρ ε : ℝ} (hκnonneg : 0 ≤ κ) (hκ : κ ≤ 1) (hρ : ρ ≤ 1)
    (hεsmall : ε ≤ 1/12) (hερ : 6*ε ≤ ρ)
    {e v w₁ w₂ : V} (he : ‖e‖ = 1)
    (hv : ‖v-e‖ ≤ ε) (hw₁ : ‖w₁-(-e)‖ ≤ ε) (hw₂ : ‖w₂-beamAxis‖ ≤ ε)
    {a : Sphere × Sphere} (ha : a ∈ accessAngles κ (ρ/2)) :
    let u := child v w₁ a.1.1
    let z := child u w₂ a.2.1
    1 ≤ ‖v-w₁‖ ∧ 3/4 ≤ ‖u-w₂‖ ∧ ‖u‖ ≤ 3 ∧ ‖z‖ ≤ 3 ∧
      ‖z-κ • firstAxis‖ < ρ := by
  let u₀ := child beamAxis (-beamAxis) a.1.1
  let z₀ := child u₀ beamAxis a.2.1
  let u := child v w₁ a.1.1
  let z := child u w₂ a.2.1
  have hu₀ : u₀ ∈ localCollisionCore := ha.2
  have hz₀ : ‖z₀-κ • firstAxis‖ < ρ/2 := ha.1
  have huerror : ‖u-u₀‖ ≤ 2*ε := by
    have hh := child_lipschitz v w₁ e (-e) a.1.1 (mem_sphere_zero_iff_norm.mp a.1.2)
    rw [child_opposite_unit e _ he] at hh
    have hh' : ‖u-u₀‖ ≤ ‖v-e‖+‖w₁-(-e)‖ := by
      simpa only [u,u₀,child_opposite_beam] using hh
    linarith
  have hzerror : ‖z-z₀‖ ≤ 3*ε := by
    exact (child_lipschitz u w₂ u₀ beamAxis a.2.1
      (mem_sphere_zero_iff_norm.mp a.2.2)).trans (by linarith)
  have hfirst := relative_distance_lower v w₁ e (-e)
  have hedist : ‖e-(-e)‖ = 2 := by
    rw [show e-(-e) = (2:ℝ) • e by module,norm_smul,Real.norm_ofNat,he,mul_one]
  rw [hedist] at hfirst
  have hsecond := relative_distance_lower u w₂ u₀ beamAxis
  have href := localCollisionCore_distance hu₀
  have hunorm := norm_le_two_of_near_unit axis_norms.1 hu₀
  have huupper : ‖u‖ ≤ 3 := by
    have hh := norm_sub_norm_le u u₀
    linarith
  have hzclose : ‖z-κ • firstAxis‖ < ρ := by
    have heq : z-κ • firstAxis = (z-z₀)+(z₀-κ • firstAxis) := by module
    have hh := norm_add_le (z-z₀) (z₀-κ • firstAxis)
    rw [← heq] at hh
    linarith
  have hzupper : ‖z‖ ≤ 3 := by
    have hh := norm_sub_norm_le z (κ • firstAxis)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκnonneg,axis_norms.1,mul_one] at hh
    linarith
  exact ⟨by linarith,by linarith,huupper,hzupper,hzclose⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end OAI
