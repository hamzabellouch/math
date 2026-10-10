import OAI.MathematicalPhysics.Boltzmann.Branching.RetainedAxialDecay

namespace OAI

/-! # Vanishing of the quantitative axial-decay bound -/

noncomputable section

open Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem axial_decay_bound_tendsto (K γ M α q : ℝ) :
    Tendsto (fun j : ℕ =>
      ENNReal.ofReal ((4*K*M/(γ^2*((j:ℝ)+1)^2))*JetGaussianProduct.coefficient)*
        SheetTotal.bound q (2*Real.exp (16*(1+α)^2))) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have h' : Tendsto (fun j : ℕ =>
      (4*K*M/γ^2)*(1/((j:ℝ)+1))^2*JetGaussianProduct.coefficient) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,zero_mul] using
      (h.const_mul (4*K*M/γ^2)).mul_const JetGaussianProduct.coefficient
  have he := ENNReal.continuous_ofReal.continuousAt.tendsto.comp h'
  simp only [Function.comp_def,ENNReal.ofReal_zero] at he
  have hm := ENNReal.Tendsto.const_mul he
    (Or.inr (SheetTotal.bound_lt_top q (2*Real.exp (16*(1+α)^2))).ne)
  simp only [mul_zero] at hm
  convert hm using 1
  funext j
  rw [mul_comm (SheetTotal.bound _ _)]
  congr 2
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow,one_mul]
  ring

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
