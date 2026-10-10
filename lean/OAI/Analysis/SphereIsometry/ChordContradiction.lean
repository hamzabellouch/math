import OAI.Analysis.SphereIsometry.LargeChord
import OAI.Analysis.SphereIsometry.SmallChord

namespace OAI

/-! A genuinely aligned positive-defect configuration is impossible. -/

namespace Tingley

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {f : UnitSphere X ≃ᵢ UnitSphere Y} {y : UnitSphere X} {t M : ℝ}

/-- The global bound and the actual aligned chords contradict one another.
The two small-regime inequalities are proved from the original and literal
inverse configurations; neither is an additional caller premise. -/
theorem alignedConfiguration_impossible (hM : 0 < M) (ht : 0 < t ∧ t < 1)
    (hb : HasDefectBound f M) (C : AlignedConfiguration f y t M) : False := by
  obtain ⟨hA, hB⟩ := C.small_ratios hM ht hb
  have heA := C.small_secant_product hM ht hb hB
  have heB : 1 - t ≤ C.d * C.B * (1 - C.A) := by
    have hA' : C.inverse.B ≤ 1 - t := by
      simpa only [AlignedConfiguration.inverse_B] using hA
    have h := C.inverse.small_secant_product hM ht hb.symm hA'
    simpa only [AlignedConfiguration.inverse_d, AlignedConfiguration.inverse_A,
      AlignedConfiguration.inverse_B] using h
  have hx : ‖t • (y : X) + C.p • (C.v : X)‖ = 1 := by
    rw [← C.x_eq]
    exact C.x.property
  have hfx : ‖t • (f y : Y) + C.s • (C.w : Y)‖ = 1 := by
    rw [← C.fx_eq]
    exact (f C.x).property
  have hleft : (1 - t) • (y : X) + C.r • (C.v : X) = (y : X) - (C.z : X) := by
    rw [C.z_eq]
    module
  have hright : (1 - t) • (f y : Y) + C.u • (C.w : Y) =
      (f y : Y) - (f C.z : Y) := by
    rw [C.fz_eq]
    module
  have hiso : ‖(1 - t) • (y : X) + C.r • (C.v : X)‖ =
      ‖(1 - t) • (f y : Y) + C.u • (C.w : Y)‖ := by
    rw [hleft, hright]
    exact (sphere_norm_sub f y C.z).symm
  exact smallChord_contradiction (y : X) (C.v : X) (f y : Y) (C.w : Y)
    (t := t) (ε := 1 - t) (d := C.d) (A := C.A) (B := C.B)
    ht.2 rfl C.p_pos C.r_pos C.s_pos C.u_pos rfl C.chord_sum C.chord_le_two
    rfl rfl (C.A_add_B_lt_one hM) hA hB heA heB y.property (f y).property hx hfx hiso

end Tingley

end OAI
