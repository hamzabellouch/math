import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

namespace Invariant233
namespace CircleCharacterDynamics

local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem representative_coe (x : ℝ) : rep (x : Circle) = Int.fract x := by
  simp [AddCircle.coe_equivIco_mk_apply]

theorem coe_representative (x : Circle) : ((rep x : ℝ) : Circle) = x :=
  AddCircle.coe_equivIco

theorem representative_add_real (x : Circle) (t : ℝ) :
    rep (x + (t : Circle)) = Int.fract (rep x + t) := by
  rw [← representative_coe]
  congr 1
  rw [AddCircle.coe_add, coe_representative]

theorem zsmul_real_phase (q : ℤ) (θ : ℝ) :
    q • (θ : Circle) = ((Int.fract ((q : ℝ) * θ) : ℝ) : Circle) := by
  rw [AddCircle.coe_fract]
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := q) (x := θ)).symm

theorem character_orbit_representative (q v : ℤ) (θ : ℝ) (x : Circle) :
    rep (q • (x + v • (θ : Circle))) =
      Int.fract (rep (q • x) + (v : ℝ) * Int.fract ((q : ℝ) * θ)) := by
  rw [zsmul_add, smul_comm q v, zsmul_real_phase]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  exact representative_add_real _ _

theorem zsmul_rational_eq_zero {q d : ℤ} (hd : d ≠ 0) (hdq : d ∣ q) (r : ℤ) :
    q • (((r : ℝ) / (d : ℝ) : ℝ) : Circle) = 0 := by
  obtain ⟨k, rfl⟩ := hdq
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have he : ((d * k : ℤ) : ℝ) * ((r : ℝ) / (d : ℝ)) = ((k * r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨k * r, ?_⟩
  simp [zsmul_eq_mul]

theorem character_rational_translation {q d : ℤ} (hd : d ≠ 0) (hdq : d ∣ q)
    (r : ℤ) (x : Circle) :
    rep (q • (x + (((r : ℝ) / (d : ℝ) : ℝ) : Circle))) = rep (q • x) := by
  rw [zsmul_add, zsmul_rational_eq_zero hd hdq r, add_zero]

end CircleCharacterDynamics
end Invariant233

end OAI
