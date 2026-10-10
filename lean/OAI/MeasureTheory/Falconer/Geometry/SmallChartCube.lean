import OAI.MeasureTheory.Falconer.Geometry.DyadicCube

namespace OAI

/-! # A fixed unit cube for the small gnomonic chart -/

namespace Falconer
open Set Metric MeasureTheory

noncomputable def smallChartCube (d : ℕ) : DyadicCube d :=
  ⟨WithLp.toLp 2 (fun _ => -(1/2:ℝ)),1⟩

lemma smallChartCube_side (d : ℕ) : (smallChartCube d).side = 1 := rfl

lemma smallChartCube_center (d : ℕ) : (smallChartCube d).center = 0 := by
  ext i
  change -(1/2:ℝ)+1/2 = 0
  ring

lemma mem_smallChartCube {d : ℕ} {x : Space d} (hx : ‖x‖ ≤ 1/4) :
    x ∈ (smallChartCube d).carrier := by
  intro i
  have hi : |x i| ≤ 1/4 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le x i).trans hx
  change -(1/2:ℝ) ≤ x i ∧ x i < -(1/2:ℝ)+1
  constructor <;> linarith [abs_le.mp hi]

lemma smallChartCube_norm {d : ℕ} {x : Space d} (hx : x ∈ (smallChartCube d).carrier) :
    ‖x‖ ≤ Real.sqrt d+1 := by
  have hc := (smallChartCube d).center_mem (by norm_num [smallChartCube])
  have hd := (smallChartCube d).dist_le (by norm_num [smallChartCube]) hx hc
  rw [smallChartCube_center,dist_zero_right,smallChartCube_side,mul_one] at hd
  linarith

lemma smallChartCube_full {d : ℕ} (μ : Measure (Space d))
    (hμ : ∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) : μ (smallChartCube d).carrierᶜ = 0 := by
  apply measure_mono_null (show (smallChartCube d).carrierᶜ ⊆ {x | ¬ ‖x‖ ≤ 1/4} from ?_)
    (ae_iff.mp hμ)
  intro x hx hb
  exact hx (mem_smallChartCube hb)

end Falconer

end OAI
