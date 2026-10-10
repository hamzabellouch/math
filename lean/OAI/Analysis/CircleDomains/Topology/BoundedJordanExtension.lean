import OAI.Analysis.CircleDomains.Topology.CenteredJordanCoordinate

namespace OAI

/-! A centered Jordan coordinate has a continuous extension taking
values in the closed unit disk, including outside the terminal collar. -/

open Set Function

noncomputable section
namespace CircleDomainRigidity

 def closedDiskClamp (z : ℂ) : ℂ := (max 1 ‖z‖)⁻¹ • z

 theorem continuous_closedDiskClamp : Continuous closedDiskClamp := by
  have h : Continuous (fun z : ℂ => (max (1 : ℝ) ‖z‖)⁻¹) :=
    (continuous_const.max continuous_norm).inv₀
      (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖z‖)))
  exact h.smul continuous_id

 theorem closedDiskClamp_norm_le (z : ℂ) : ‖closedDiskClamp z‖ ≤ 1 := by
  have hp : 0 < max 1 ‖z‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    ‖closedDiskClamp z‖ = (max 1 ‖z‖)⁻¹ * ‖z‖ := by
      rw [closedDiskClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp)]
    _ ≤ (max 1 ‖z‖)⁻¹ * max 1 ‖z‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hp.le)
    _ = 1 := inv_mul_cancel₀ hp.ne'

 theorem closedDiskClamp_eq_of_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : closedDiskClamp z = z := by
  simp only [closedDiskClamp, max_eq_left hz, inv_one, one_smul]

 theorem exists_bounded_centeredJordanExtension (J : ℂ ≃ₜ ℂ) {b : Sphere}
    (hb : b ∈ ((↑) : ℂ → Sphere) '' jordanInterior J) :
    ∃ F : C(Sphere, ℂ),
      EqOn F (centeredJordanCoordinate J b)
        (closure (((↑) : ℂ → Sphere) '' jordanInterior J)) ∧ ∀ x, ‖F x‖ ≤ 1 := by
  obtain ⟨F, hF⟩ := exists_centeredJordanExtension J hb
  let Q : C(Sphere, ℂ) := ⟨closedDiskClamp ∘ F, continuous_closedDiskClamp.comp F.continuous⟩
  refine ⟨Q, ?_, fun x => closedDiskClamp_norm_le (F x)⟩
  intro x hx
  change closedDiskClamp (F x) = centeredJordanCoordinate J b x
  rw [closedDiskClamp_eq_of_norm_le, hF hx]
  rw [hF hx]
  exact centeredJordanCoordinate_norm_le J hb hx

end CircleDomainRigidity

end

end OAI
