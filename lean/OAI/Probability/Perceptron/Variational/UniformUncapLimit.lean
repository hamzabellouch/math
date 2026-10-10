import Mathlib
import OAI.Probability.Perceptron.Model

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace SphericalPerceptronFreeEnergy

lemma tendsto_zero_of_uniform_inverse_cap (f : ℕ→ℝ) (g : ℝ→ℕ→ℝ) {C : ℝ}
    (hC : 0≤C) (hbound : ∀ Λ,1≤Λ→∀ j,|f j-g Λ j|≤C/Λ)
    (hlim : ∀ Λ,1≤Λ→Tendsto (g Λ) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let Λ:=1+2*C/ε
  have hΛ : 1≤Λ:=by dsimp [Λ]; linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤2) hC) hε.le]
  have hΛp : 0<Λ:=lt_of_lt_of_le zero_lt_one hΛ
  have hsmall : C/Λ<ε/2 := by
    apply (div_lt_iff₀ hΛp).mpr
    dsimp [Λ]
    field_simp
    nlinarith
  obtain ⟨N,hN⟩:=Metric.tendsto_atTop.mp (hlim Λ hΛ) (ε/2) (half_pos hε)
  refine ⟨N,fun j hj=>?_⟩
  have he:=hN j hj
  rw [Real.dist_eq,sub_zero] at he ⊢
  calc
    |f j|≤|f j-g Λ j|+|g Λ j|:=by simpa using abs_add_le (f j-g Λ j) (g Λ j)
    _≤C/Λ+|g Λ j|:=add_le_add (hbound Λ hΛ j) le_rfl
    _<ε:=by linarith
end SphericalPerceptronFreeEnergy

end

end OAI
