import OAI.Geometry.NodalSets.Elliptic.RealDivergenceEnergyBound

namespace OAI

namespace Yau
open MeasureTheory
noncomputable section

theorem real_divergence_difference_energy_absorption_ae {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (m K : ℝ) (hm : 0 < m)
    (T V R D P G : Fin 4 → α → ℝ) (F b : α → ℝ)
    (hT : ∀ j, MemLp (T j) 2 μ) (hV : ∀ j, MemLp (V j) 2 μ)
    (hR : ∀ j, MemLp (R j) 2 μ) (hP : ∀ j, MemLp (P j) 2 μ)
    (hG : ∀ j, MemLp (G j) 2 μ)
    (hDP : ∀ j, Integrable (fun x ↦ D j x*P j x) μ)
    (hF : MemLp F 2 μ) (hb : MemLp b 2 μ)
    (hlow : ∀ᵐ x ∂μ, (m/2)*(∑ j, (T j x)^2) ≤
      (∑ j, D j x*P j x)+K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2)))
    (htest : (∫ x, (b x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (hPtest : (∑ j, ∫ x, (P j x)^2 ∂μ) ≤
      2*(∑ j, ∫ x, (T j x)^2 ∂μ)+8*(∑ j, ∫ x, (R j x)^2 ∂μ))
    (heq : (∑ j, ∫ x, D j x*P j x ∂μ)=-(∫ x, F x*b x ∂μ)-
      ∑ j, ∫ x, G j x*P j x ∂μ) :
    (∑ j, ∫ x, (T j x)^2 ∂μ) ≤ (4/m)*
      ((16/m)*((∫ x, (F x)^2 ∂μ)+(∑ j, ∫ x, (G j x)^2 ∂μ))+
        K*(∑ j, ∫ x, (V j x)^2 ∂μ)+(K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ)) := by
  have hiT := integrable_finsetSum Finset.univ (fun j _ ↦ (hT j).integrable_sq)
  have hiV := integrable_finsetSum Finset.univ (fun j _ ↦ (hV j).integrable_sq)
  have hiR := integrable_finsetSum Finset.univ (fun j _ ↦ (hR j).integrable_sq)
  have hiD := integrable_finsetSum Finset.univ (fun j _ ↦ hDP j)
  have hiVR : Integrable (fun x ↦ (∑ j, (V j x)^2)+(∑ j, (R j x)^2)) μ := hiV.add hiR
  have hiK : Integrable (fun x ↦ K*((∑ j, (V j x)^2)+(∑ j, (R j x)^2))) μ := hiVR.const_mul K
  have hl := integral_mono_ae (hiT.const_mul (m/2)) (hiD.add hiK) hlow
  dsimp only [Pi.add_apply] at hl
  rw [integral_const_mul,integral_add hiD hiK,integral_const_mul,integral_add hiV hiR,
    integral_finsetSum _ (fun j _ ↦ (hT j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hV j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ (hR j).integrable_sq),
    integral_finsetSum _ (fun j _ ↦ hDP j),heq] at hl
  have hy := real_integral_young μ F b hF hb (m/16) (by positivity)
  have hys := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦
    real_integral_young μ (G j) (P j) (hG j) (hP j) (m/16) (by positivity))
  simp only [Finset.sum_neg_distrib,Finset.sum_add_distrib,← Finset.mul_sum] at hys
  have hb' := mul_le_mul_of_nonneg_left htest (show 0 ≤ m/16 by positivity)
  have hP' := mul_le_mul_of_nonneg_left hPtest (show 0 ≤ m/16 by positivity)
  have hc : 1/(m/16)=16/m := by ring
  rw [hc] at hy hys
  have hpre : (m/4)*(∑ j, ∫ x, (T j x)^2 ∂μ) ≤
      (16/m)*((∫ x, (F x)^2 ∂μ)+(∑ j, ∫ x, (G j x)^2 ∂μ))+
        K*(∑ j, ∫ x, (V j x)^2 ∂μ)+(K+m)*(∑ j, ∫ x, (R j x)^2 ∂μ) := by
    nlinarith only [hl,hy,hys,hb',hP']
  have hscale := mul_le_mul_of_nonneg_left hpre (show 0 ≤ 4/m by positivity)
  have hcancel : (4/m)*(m/4)=1 := by field_simp
  simpa only [← mul_assoc,hcancel,one_mul] using hscale

end
end Yau

end OAI
