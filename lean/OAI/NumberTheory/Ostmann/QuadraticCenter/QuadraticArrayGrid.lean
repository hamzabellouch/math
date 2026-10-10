import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterGrid
import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticAtom

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def smoothQuadraticSum {ω : Type*} (I : Finset ω) (a : ω → ℂ) (κ : ω → ℝ)
    (h θ R : ℝ) : ℂ := ∑ w ∈ I, quadraticAtom (a w) (κ w) h θ R

def quadraticGridConstant {ω : Type*} (I : Finset ω) (a : ω → ℂ) (κ : ω → ℝ) : ℝ :=
  ∑ w ∈ I, ‖a w‖ * cutoffFourierBound * ((2 * Real.pi) * |κ w| + (1 + |κ w|))

theorem quadraticGridConstant_nonneg {ω : Type*} (I : Finset ω) (a : ω → ℂ) (κ : ω → ℝ) :
    0 ≤ quadraticGridConstant I a κ := by
  apply Finset.sum_nonneg
  intro w hw
  have hC := cutoffFourierBound_pos.le
  positivity

theorem smoothQuadraticSum_parameters {ω : Type*} (I : Finset ω) (a : ω → ℂ) (κ : ω → ℝ)
    {R R' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R') (h θ θ' : ℝ) :
    ‖smoothQuadraticSum I a κ h θ R - smoothQuadraticSum I a κ h θ' R'‖ ≤
      quadraticGridConstant I a κ * (|θ - θ'| + |R - R'|) := by
  unfold smoothQuadraticSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ I, ‖quadraticAtom (a w) (κ w) h θ R - quadraticAtom (a w) (κ w) h θ' R'‖ :=
      norm_sum_le _ _
    _ ≤ ∑ w ∈ I, (‖a w‖ * cutoffFourierBound * ((2 * Real.pi) * |κ w| + (1 + |κ w|))) *
        (|θ - θ'| + |R - R'|) := by
      apply Finset.sum_le_sum
      intro w hw
      apply (quadraticAtom_parameters_lipschitz hR hR' (a w) (κ w) h θ θ').trans
      have hu : 0 ≤ (2 * Real.pi) * |κ w| := by positivity
      have hv : 0 ≤ 1 + |κ w| := by positivity
      have hde : (2 * Real.pi) * |κ w| * |θ - θ'| + (1 + |κ w|) * |R - R'| ≤
          ((2 * Real.pi) * |κ w| + (1 + |κ w|)) * (|θ - θ'| + |R - R'|) := by
        nlinarith [mul_nonneg hu (abs_nonneg (R - R')), mul_nonneg hv (abs_nonneg (θ - θ'))]
      have hc := mul_le_mul_of_nonneg_left hde (mul_nonneg (norm_nonneg (a w)) cutoffFourierBound_pos.le)
      simpa only [mul_assoc] using hc
    _ = _ := by rw [← Finset.sum_mul]; rfl

def quadraticArrayGrid {β ω : Type*} (I : Finset ω)
    (a : β → ω → ℂ) (κ : β → ω → ℝ) (h : β → ℝ) (B m : ℕ) : Finset (β → ℂ) := by
  classical
  exact ((parameterGrid 0 1 m).product (parameterGrid 1 B m)).image
    (fun z => fun b => smoothQuadraticSum I (a b) (κ b) (h b) z.1 z.2)

theorem quadraticArrayGrid_card {β ω : Type*} (I : Finset ω)
    (a : β → ω → ℂ) (κ : β → ω → ℝ) (h : β → ℝ) (B m : ℕ) :
    (quadraticArrayGrid I a κ h B m).card ≤ (m + 1) * (B * m + 1) := by
  classical
  exact Finset.card_image_le.trans (parameter_pair_card_le B m)

theorem exists_near_quadraticArrayGrid {β ω : Type*} (I : Finset ω)
    (a : β → ω → ℂ) (κ : β → ω → ℝ) (h : β → ℝ)
    {B m : ℕ} (hm : 0 < m) {θ R : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ B) :
    ∃ b₀ ∈ quadraticArrayGrid I a κ h B m,
      ∀ b : β, ‖smoothQuadraticSum I (a b) (κ b) (h b) θ R - b₀ b‖ ≤
        2 * quadraticGridConstant I (a b) (κ b) / m := by
  classical
  obtain ⟨z, hz, hθ, hR, hzR⟩ := exists_near_parameter_pair hm hθ0 hθ1 hR1 hRB
  refine ⟨fun b => smoothQuadraticSum I (a b) (κ b) (h b) z.1 z.2,
    Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
  intro b
  calc
    _ ≤ quadraticGridConstant I (a b) (κ b) * (|θ - z.1| + |R - z.2|) :=
      smoothQuadraticSum_parameters I (a b) (κ b) hR1 hzR (h b) θ z.1
    _ ≤ quadraticGridConstant I (a b) (κ b) * (1 / (m : ℝ) + 1 / m) :=
      mul_le_mul_of_nonneg_left (add_le_add hθ hR) (quadraticGridConstant_nonneg _ _ _)
    _ = _ := by ring

end Ostmann.QuadraticCenter

end

end OAI
