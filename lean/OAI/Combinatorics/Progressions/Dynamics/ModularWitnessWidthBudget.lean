import OAI.Combinatorics.Progressions.Sampling.LayerSamplerWitnessScale

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem modularWitnessWidthBudget {I : Type*} [Fintype I]
    (width : I → ℝ) {A cap κ D V E : ℝ}
    (hA : 0 < A) (hcap : 0 ≤ cap) (hκ : 0 < κ)
    (hD : 0 ≤ D) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp D)
    (hcapV : cap ≤ Real.exp V) (hκE : κ⁻¹ ≤ Real.exp E)
    (hwidth : ∀ i, 8 * A * Real.exp (D + V + E + 4) ≤ width i) :
    1 ≤ Real.exp (D + V + E + 4) ∧
      (∀ i, 8 * A * cap ≤ width i) ∧
      (∑ i, 16 * A * cap / width i) ≤ κ / 2 := by
  let W := Real.exp (D + V + E + 4)
  have hW : 0 < W := Real.exp_pos _
  have hW1 : 1 ≤ W := Real.one_le_exp (by positivity)
  have hcapW : cap ≤ W := hcapV.trans (Real.exp_le_exp.mpr (by linarith))
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbudget : 4 * (Fintype.card I : ℝ) * cap / κ ≤ W := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 4 * Real.exp D * Real.exp V * Real.exp E := by gcongr
      _ = _ := by
        dsimp only [W]
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hlocal (i : I) : 16 * A * cap / width i ≤ 2 * cap / W := by
    have hden : 0 < 8 * A * W := by positivity
    calc
      _ ≤ 16 * A * cap / (8 * A * W) :=
        div_le_div_of_nonneg_left (by positivity) hden (hwidth i)
      _ = _ := by field_simp; ring
  refine ⟨hW1, fun i => (mul_le_mul_of_nonneg_left hcapW (by positivity)).trans (hwidth i), ?_⟩
  calc
    _ ≤ ∑ i : I, 2 * cap / W := Finset.sum_le_sum (fun i _ => hlocal i)
    _ = (Fintype.card I : ℝ) * (2 * cap / W) := by simp
    _ ≤ κ / 2 := by
      have hb := (div_le_iff₀ hκ).mp hbudget
      rw [show (Fintype.card I : ℝ) * (2 * cap / W) =
        (2 * Fintype.card I * cap) / W by ring]
      apply (div_le_iff₀ hW).mpr
      nlinarith

end Erdos3

end

end OAI
