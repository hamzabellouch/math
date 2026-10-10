import OAI.Geometry.NodalSets.Elliptic.RealDifferenceCoercivity
import OAI.Geometry.NodalSets.Elliptic.RealL2PairingRepresentatives

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_integral_young {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u v : α → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ)
    (e : ℝ) (he : 0 < e) :
    -(∫ x, u x*v x ∂μ) ≤ e*(∫ x, (v x)^2 ∂μ)+(1/e)*(∫ x, (u x)^2 ∂μ) := by
  rw [← integral_neg,← integral_const_mul,← integral_const_mul,
    ← integral_add (hv.integrable_sq.const_mul e) (hu.integrable_sq.const_mul (1/e))]
  apply integral_mono (hu.integrable_mul hv).neg
    ((hv.integrable_sq.const_mul e).add (hu.integrable_sq.const_mul (1/e)))
  intro x
  change -(u x*v x) ≤ e*(v x)^2+(1/e)*(u x)^2
  simpa only [one_mul,one_pow,mul_comm (v x) (u x)] using
    real_young_coefficient e 1 1 (v x) (u x) he (by norm_num) (by norm_num)

theorem real_difference_energy_absorption {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (m K : ℝ) (hm : 0 < m) (T V R D P : Fin 4 → α → ℝ) (F b : α → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) (hV : ∀ j, MemLp (V j) 2 μ)
    (hR : ∀ j, MemLp (R j) 2 μ) (hDP : ∀ j, Integrable (fun x ↦ D j x*P j x) μ)
    (hF : MemLp F 2 μ) (hb : MemLp b 2 μ)
    (hlow : ∀ x, (m/2)*(∑ j, (T j x)^2) ≤
      (∑ j, D j x*P j x)+K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)))
    (htest : (∫ x, (b x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (heq : (∑ j, ∫ x, D j x*P j x ∂μ)=-(∫ x, F x*b x ∂μ)) :
    (∑ j, ∫ x, (T j x)^2 ∂μ) ≤ (4/m)*
      ((8/m)*(∫ x, (F x)^2 ∂μ)+K*(∑ j, ∫ x, (V j x)^2 ∂μ)+
        (K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ)) := by
  have hiT := integrable_finsetSum Finset.univ (fun j _ ↦ (hT j).integrable_sq)
  have hiV := integrable_finsetSum Finset.univ (fun j _ ↦ (hV j).integrable_sq)
  have hiR := integrable_finsetSum Finset.univ (fun j _ ↦ (hR j).integrable_sq)
  have hiD := integrable_finsetSum Finset.univ (fun j _ ↦ hDP j)
  have hiVR : Integrable (fun x ↦ (∑ j, (V j x)^2)+(∑ j, (R j x)^2)) μ := hiV.add hiR
  have hiK : Integrable (fun x ↦ K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2))) μ := hiVR.const_mul K
  have hl := integral_mono (hiT.const_mul (m/2)) (hiD.add hiK) hlow
  dsimp only [Pi.add_apply] at hl
  rw [integral_const_mul,integral_add hiD hiK,
    integral_const_mul,integral_add hiV hiR,
    integral_finsetSum _ (fun j _ ↦ (hT j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hV j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hR j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ hDP j),heq] at hl
  have hy := real_integral_young μ F b hF hb (m/8) (by positivity)
  have hb' := mul_le_mul_of_nonneg_left htest (show 0 ≤ m/8 by positivity)
  have hc : 1/(m/8)=8/m := by ring
  rw [hc] at hy
  have hpre : (m/4)*(∑ j, ∫ x, (T j x)^2 ∂μ) ≤
      (8/m)*(∫ x, (F x)^2 ∂μ)+K*(∑ j, ∫ x, (V j x)^2 ∂μ)+
        (K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hpre (show 0 ≤ 4/m by positivity)
  have hcancel : (4/m)*(m/4)=1 := by field_simp
  simpa only [← mul_assoc,hcancel,one_mul] using hscale

end
end Yau

end OAI
