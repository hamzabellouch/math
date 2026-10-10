import OAI.MeasureTheory.Falconer.Geometry.ProjectionDilation

namespace OAI

/-! # Put compact projected supports in a fixed unit cube -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

noncomputable def centeredUnitCube (d : ℕ) : DyadicCube d :=
  ⟨WithLp.toLp 2 (fun _ => -(1/2:ℝ)),1⟩

theorem mem_centeredUnitCube_of_norm {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (centeredUnitCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

theorem centeredUnitCube_norm_bound {x : Space d}
    (hx : x ∈ (centeredUnitCube d).carrier) : ‖x‖ ≤ Real.sqrt d := by
  have hzero : (0 : Space d) ∈ (centeredUnitCube d).carrier :=
    mem_centeredUnitCube_of_norm (by simp)
  have hd := (centeredUnitCube d).dist_le (by norm_num [centeredUnitCube]) hx hzero
  simpa [centeredUnitCube] using hd

theorem compact_projection_into_unitCube (E : Set (Space d)) (hE : IsCompact E)
    (P : Space d →L[ℝ] Space m) :
    ∃ a : ℝ, 0 < a ∧ ‖a • P‖ ≤ 1 ∧
      ∀ x ∈ E, (a • P) x ∈ (centeredUnitCube m).carrier := by
  obtain ⟨M,hM,hbound⟩ := (hE.image P.continuous).isBounded.exists_pos_norm_le
  let a := (4*(M+‖P‖+1))⁻¹
  have hden : 0 < 4*(M+‖P‖+1) := by positivity
  have ha : 0 < a := inv_pos.mpr hden
  refine ⟨a,ha,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    change (4*(M+‖P‖+1))⁻¹*‖P‖ ≤ 1
    rw [inv_mul_le_iff₀ hden]
    nlinarith only [hM,norm_nonneg P]
  · intro x hx
    apply mem_centeredUnitCube_of_norm
    rw [smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    calc
      a * ‖P x‖ ≤ a*M := mul_le_mul_of_nonneg_left (hbound _ ⟨x,hx,rfl⟩) ha.le
      _ ≤ 1/4 := by
        change (4*(M+‖P‖+1))⁻¹*M ≤ 1/4
        rw [inv_mul_le_iff₀ hden]
        nlinarith only [norm_nonneg P]

end Falconer

end OAI
