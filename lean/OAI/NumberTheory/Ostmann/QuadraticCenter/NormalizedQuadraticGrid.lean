import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticScale

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def normalizedQuadraticArrayGrid {β : Type*} (a : β → ℕ → ℂ)
    (q h : β → ℝ) (P : ℕ) (B m : ℕ) : Finset (β → ℂ) := by
  classical
  exact ((parameterGrid 0 1 m).product (parameterGrid 1 B m)).image
    (fun z => fun b => normalizedSmoothQuadraticSum P (Real.sqrt (z.2 / q b))
      (a b) ((h b + z.1) * q b))

theorem normalizedQuadraticArrayGrid_card {β : Type*} (a : β → ℕ → ℂ)
    (q h : β → ℝ) (P B m : ℕ) :
    (normalizedQuadraticArrayGrid a q h P B m).card ≤ (m + 1) * (B * m + 1) := by
  classical
  exact Finset.card_image_le.trans (parameter_pair_card_le B m)

theorem exists_near_normalizedQuadraticArrayGrid {β : Type*} (a : β → ℕ → ℂ)
    (q h : β → ℝ) (P W : ℕ) (hq : ∀ b, 0 < q b) {B m : ℕ} (hm : 0 < m)
    {θ R : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ B)
    (hW : ∀ b, ⌊Real.sqrt ((B : ℝ) / q b)⌋₊ ≤ W) :
    ∃ b₀ ∈ normalizedQuadraticArrayGrid a q h P B m, ∀ b : β,
      ‖normalizedSmoothQuadraticSum P (Real.sqrt (R / q b)) (a b) ((h b + θ) * q b) - b₀ b‖ ≤
        2 * Real.sqrt (q b) * quadraticGridConstant
          ((Finset.Ioc 0 W).filter (fun w => P ∣ w)) (a b) (fun w => q b * (w : ℝ) ^ 2) / m := by
  classical
  obtain ⟨z, hz, hθ, hR, hzR⟩ := exists_near_parameter_pair hm hθ0 hθ1 hR1 hRB
  have hzB : z.2 ≤ (B : ℝ) :=
    (mem_parameterGrid_bounds hm (Finset.mem_product.mp hz).2).2
  refine ⟨fun b => normalizedSmoothQuadraticSum P (Real.sqrt (z.2 / q b))
      (a b) ((h b + z.1) * q b), Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
  intro b
  dsimp only
  have hwR : ⌊Real.sqrt (R / q b)⌋₊ ≤ W :=
    (Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hRB (hq b).le))).trans (hW b)
  have hwz : ⌊Real.sqrt (z.2 / q b)⌋₊ ≤ W :=
    (Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hzB (hq b).le))).trans (hW b)
  rw [normalizedSmoothQuadraticSum_eq_grid_sum (by linarith) (hq b) hwR,
    normalizedSmoothQuadraticSum_eq_grid_sum (by linarith) (hq b) hwz,
    ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  let I := (Finset.Ioc 0 W).filter (fun w => P ∣ w)
  have hc := smoothQuadraticSum_parameters I (a b) (fun w => q b * (w : ℝ) ^ 2)
    hR1 hzR (h b) θ z.1
  have hC := quadraticGridConstant_nonneg I (a b) (fun w => q b * (w : ℝ) ^ 2)
  calc
    _ ≤ Real.sqrt (q b) * (quadraticGridConstant I (a b) (fun w => q b * (w : ℝ) ^ 2) *
        (|θ - z.1| + |R - z.2|)) := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (q b) * (quadraticGridConstant I (a b) (fun w => q b * (w : ℝ) ^ 2) *
        (1 / (m : ℝ) + 1 / m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hθ hR) hC)
        (Real.sqrt_nonneg _)
    _ = _ := by dsimp [I]; ring

end Ostmann.QuadraticCenter

end

end OAI
