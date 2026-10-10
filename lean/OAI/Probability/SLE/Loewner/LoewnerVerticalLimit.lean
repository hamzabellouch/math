import OAI.Probability.SLE.Loewner.LoewnerInverseStability

namespace OAI

/-! The zero-driver inverse trajectory, and convergence to it on the
imaginary axis under a uniform perturbation of the driving function. -/
noncomputable section
open Set Filter Complex
open scoped Topology NNReal

namespace SLEExactGauge

def verticalReversePath (y s : ℝ) : ℂ := (Real.sqrt (y^2+4*s) : ℂ)*I

lemma verticalReversePath_zero {y : ℝ} (hy : 0 < y) :
    verticalReversePath y 0=(y:ℂ)*I := by
  simp [verticalReversePath,Real.sqrt_sq hy.le]

lemma verticalReversePath_derivative {y s : ℝ} (hy : 0 < y) (hs : 0 ≤ s) :
    HasDerivAt (verticalReversePath y)
      (reverseField y 0 (verticalReversePath y s)) s := by
  have hp : 0 < y^2+4*s := by positivity
  have hr : 0 < Real.sqrt (y^2+4*s) := Real.sqrt_pos.mpr hp
  have hle : y ≤ Real.sqrt (y^2+4*s) := by
    calc
      y = Real.sqrt (y^2) := (Real.sqrt_sq hy.le).symm
      _ ≤ Real.sqrt (y^2+4*s) := Real.sqrt_le_sqrt (by linarith)
  have hd := (((hasDerivAt_const s (y^2)).add
    ((hasDerivAt_id s).const_mul 4)).sqrt hp.ne').ofReal_comp.mul_const I
  have hd' : HasDerivAt (verticalReversePath y)
      ((((4)/(2*Real.sqrt (y^2+4*s)) : ℝ) : ℂ)*I) s := by
    convert! hd using 1
    simp only [Pi.add_apply, id_eq, zero_add, mul_one]
  have he : reverseField y 0 (verticalReversePath y s) =
      (((4)/(2*Real.sqrt (y^2+4*s)) : ℝ) : ℂ)*I := by
    have hi : y ≤ (verticalReversePath y s).im := by
      simpa [verticalReversePath] using hle
    rw [reverseField,reverseCenter_eq hi,Complex.ofReal_zero,sub_zero]
    dsimp [verticalReversePath]
    have hc : (Real.sqrt (y^2+4*s) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp [hc]
    norm_num [Complex.I_sq]
  exact he ▸ hd'

theorem IsCapacityTwoWitness.inverse_vertical_approximation
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) {y : ℝ} (hy : 0 < y)
    (δ : ℝ) (hU : ∀ t ∈ Icc 0 T, |U t| ≤ δ) :
    dist (F T ((y:ℂ)*I)) (verticalReversePath y T) ≤
      gronwallBound 0 (4*y⁻¹^2) (2*y⁻¹^2*δ) T := by
  apply h.inverse_approximation_bound T hy ((y:ℂ)*I) (by simp)
    (fun _ => 0) δ (by simpa only [sub_zero] using hU)
    (verticalReversePath y) (verticalReversePath_zero hy)
  intro s hs
  exact (verticalReversePath_derivative hy hs.1).hasDerivWithinAt

theorem inverse_vertical_tendsto
    (U : ℕ → ℝ≥0 → ℝ) (γ : ℕ → ℝ≥0 → ℂ)
    (G F : ℕ → ℝ≥0 → ℂ → ℂ)
    (h : ∀ n, IsCapacityTwoWitness (U n) (γ n) (G n) (F n))
    (T : ℝ≥0) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hU : ∀ n t, t ∈ Icc 0 T → |U n t| ≤ δ n)
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun n => F n T ((y:ℂ)*I)) atTop (𝓝 (verticalReversePath y T)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hb := fun n => (h n).inverse_vertical_approximation T hy (δ n) (hU n)
  have ht := (gronwallBound_continuous_ε 0 (4*y⁻¹^2) T).continuousAt.tendsto.comp
    (hδ.const_mul (2*y⁻¹^2))
  simp only [mul_zero,gronwallBound_ε0_δ0] at ht
  exact squeeze_zero (fun _ => dist_nonneg) hb ht

end SLEExactGauge

end

end OAI
